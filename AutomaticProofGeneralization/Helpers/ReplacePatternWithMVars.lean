import Lean
import AutomaticProofGeneralization.Helpers.Antiunification
import AutomaticProofGeneralization.Helpers.Naming
import AutomaticProofGeneralization.Helpers.Metavariables
import AutomaticProofGeneralization.Helpers.FunctionApplications

open Lean Elab Tactic Meta Term Command AntiUnify

initialize
  registerTraceClass `TypecheckingErrors
  registerTraceClass `Autogeneralize.abstractPattern

-- local instance {α} : ExceptToEmoji Exception α where
--   toEmoji
--   | .error _ => crossEmoji
--   | .ok _ => ""

section ReplacePatternWithMVars

/-!

This section of the file defines `replacePatternWithMVars`,
a function that traverses an expression replacing
all instances of a pattern with (different) metavariables and
abstracting relevant hypotheses.

It is loosely based on the `Lean.Meta.kabstract` from Lean's core library.

The function runs in the `ReplaceM` monad defined below,
which keeps track of relevant data during the traversal.

-/

/-- The read-only part of the `ReplaceM` monad. -/
structure ReplaceM.Context where
  /-- The local context within which new metavariables are defined. -/
  lctx : LocalContext := {}
  /-- The local instances within which new metavariables are defined. -/
  localInstances : LocalInstances := {}
  /-- Whether to abstract hypotheses in addition to replacing occurrences of the pattern with metavariables. -/
  abstractHyps : Bool := true
  /-- Whether to identify constants in the proof that depend on the one being generalized. -/
  generalizeRelatedConstants : Bool := true
  /-- The current recursion depth of the function. -/
  depth : Nat := 0
  /-- The maximum cutoff recursion depth of the function. -/
  cutOffDepth : Nat := 3

/-- The stateful part of the `ReplaceM` monad. -/
structure ReplaceM.State where
  /-- A list of terms identified to be conflicting with the one being generalized. -/
  mismatches : List Expr := []
  /-- Whether the expression has been modified during the traversal. -/
  modified : Bool := false

/-- The `ReplaceM` monad, which keeps track of relevant data needed to abstract instances of a pattern within an expression. -/
abbrev ReplaceM := ReaderT ReplaceM.Context <| StateT ReplaceM.State MetaM

/-- Adds a list of terms to the list of conflicting terms in the state. -/
def ReplaceM.addConflictingTerms (terms : List Expr) : ReplaceM Unit := do
  modify fun σ => { σ with mismatches := (terms ++ σ.mismatches).eraseDups }

/-- Return the result if the action changes the `modified` flag to `true`, return `none` otherwise. -/
def ReplaceM.withReturnIfModified {α} (act : ReplaceM α) : ReplaceM (Option α) := do
  modify ({· with modified := false})
  let result ← act
  if (← get).modified then
    return some result
  else
    return none

/-- Create a new metavariable of the given type, marking the expression as `modified` in the process. -/
def ReplaceM.mkExprMVar (type : Expr) (userName : Name := .anonymous) : ReplaceM Expr := do
  let ctx ← read
  let mvar ← mkFreshExprMVarAt ctx.lctx ctx.localInstances type (kind := .synthetic) (userName := userName)
  modify ({ · with modified := true })
  return mvar

def ReplaceM.withIncDepth {α} : ReplaceM α → ReplaceM α :=
  withReader fun ctx ↦ { ctx with depth := ctx.depth + 1 }

def ReplaceM.withoutAbstractingHypsOrGeneralizingConstants {α} : ReplaceM α → ReplaceM α :=
  withReader ({ · with abstractHyps := false, generalizeRelatedConstants := false })

def ReplaceM.run {α} (m : ReplaceM α) : MetaM (α × ReplaceM.State) := do
  ReaderT.run m { lctx := ← getLCtx, localInstances := ← getLocalInstances } |>.run {}

def ReplaceM.run' {α} (m : ReplaceM α) : MetaM α := do
  ReaderT.run m { lctx := ← getLCtx, localInstances := ← getLocalInstances } |>.run' {}

open ReplaceM in
/--
`replacePatternWithMVars` takes in an expression `e` and a pattern `p` as input
and abstracts all occurrences of `p` in `e` by replacing them with *different* metavariables,
abstracting relevant hypotheses and identifying related constants to generalize in the process.
-/
partial def replacePatternWithMVars (e : Expr) (p : Expr) : ReplaceM Expr := do
  -- the type of the pattern being generalized
  let pType ← withReducibleAndInstances <| reduce <| ← inferType p
  trace[Autogeneralize.abstractPattern] m!"Abstracting pattern {p} of type {pType}"
  let rec visit (e : Expr) : ReplaceM Expr := do
    let visitChildren : Unit → ReplaceM Expr := fun _ => do
      match e with
      | .app f a         =>
        -- it's possible that modifications to the expression during the traversal create application type mismatches
        -- so it may be necessary to identify additional terms to generalize to make the overall expression type-correct.
        let fAbs ← visit f
        let aAbs ← visit a
        if (← read).generalizeRelatedConstants then
          let expectedA ← extractArgType fAbs -- the expected type of the argument
          let inferredA ← inferType aAbs      -- the actual type of the argument
          -- if there is an application type mismatch, identify new terms to generalize
          unless ← liftM <| withoutModifyingState <| isDefEq expectedA inferredA do
            trace[TypecheckingErrors] m!"Error in typechecking: aAbs was expected to have type \n\t{expectedA} \nbut has type \n\t{inferredA}"
            -- the mismatch is probably caused because something else needs to be generalized
            -- candidate terms for generalization are identified through anti-unification
            let (_result, problemTerms) ← getTermsToGeneralize expectedA inferredA
            trace[TypecheckingErrors] m!"The mismatch can probably be fixed by generalizing the terms {problemTerms}"
            -- add the conflicting terms to the state
            ReplaceM.addConflictingTerms (problemTerms.map Prod.snd)
        return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b)
      | .proj _ _ b      => return e.updateProj! (← visit b)
      | .letE n t v b _ =>
        let tAbs ← visit t
        let vAbs ← visit v
        -- ensure that the generalized value and type are still in sync
        unless ← isDefEq tAbs (← inferType vAbs) do
          throwError m!"Expected the type of {vAbs} in `let` statement to be {tAbs}, but got {← inferType vAbs}"
        -- "withLetDecl" temporarily adds "n : tAbs" to context, storing the fvar in placeholder
        let updatedLet ← withLetDecl n tAbs vAbs fun placeholder => do
          let b := b.instantiate1 placeholder
          let bAbs ← if (←  liftM <| withoutModifyingState <| isDefEq tAbs t) then
                visit b  -- now it's safe to recurse on b (no loose bvars)
              else
                logInfo m!"tAbs {tAbs} and t {t} are not defeq"
                pure b
          return ← mkLetFVars (usedLetOnly := false) #[placeholder] bAbs-- put the "n:tAbs" back in the expression itself instead of in an external fvar

        return updatedLet
      | .lam n d b bi     =>
        let dAbs ← visit d
        -- "withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
        let updatedLambda ← withLocalDecl n bi dAbs fun placeholder => do
          let b := b.instantiate1 placeholder
          let bAbs ←
            if (←  liftM <| withoutModifyingState <| isDefEq dAbs d) then
              visit b  -- now it's safe to recurse on b (no loose bvars)
            else
              logInfo m!"dAbs {dAbs} and d {d} are not defeq"
              pure b
          return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar

        return updatedLambda
      | .forallE n d b bi =>
        let dAbs ← visit d
        -- "withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
        let updatedForAll ← withLocalDecl n bi dAbs fun placeholder => do
          let b := b.instantiate1 placeholder
          let bAbs ← visit b  -- now it's safe to recurse on b (no loose bvars)
          return ← mkForallFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
        return updatedForAll
      | e                =>
        return e

    withTraceNodeBefore `Autogeneralize.abstractPattern (fun () ↦ do pure m!"Visiting {e} at depth {(← read).depth}") do
      let mctx ← getMCtx
      -- if the expression "e" matches with the pattern being replaced ...
      if !e.isMVar && (← withReducibleAndInstances <| isDefEq e p) then
        -- since the type of `p` may be slightly different each time depending on the context it's in, we specialize it each time
        let pType ← instantiateMVars pType
        setMCtx mctx
        trace[Autogeneralize.abstractPattern] m!"{checkEmoji} Found pattern {p}, replacing with mvar"
        mkExprMVar pType (userName := placeholderName) -- replace every occurrence of pattern with mvar
      -- otherwise, "e" might contain the pattern...
      else
        setMCtx mctx
        -- so that other matches are still possible.
        let e' ← visitChildren ()

        if (← read).depth > (← read).cutOffDepth || !(← read).abstractHyps then
          return e'
        else
          -- if the current expression contains the pattern in its type (but not its term),
          -- we abstract it as a hypothesis of the generalized type

          -- the type of the expression being generalized
          let e'Type ← inferType e'
          trace[Autogeneralize.abstractPattern] m!"🔍 Inspecting type {e'Type}"
          -- visiting the type of the expression, replacing any occurrences of the pattern with metavariables
          -- `withReturnIfModified` will return `none` if the type is not modified
          let some e'TypeAbs ←
            withReturnIfModified <| withIncDepth <| withoutAbstractingHypsOrGeneralizingConstants <|
              visit e'Type | return e'
          -- the previous pass on `e'Type` visited without abstracting hypotheses in `e'Type` for efficiency reasons
          -- if occurrences of the pattern are detected in the type, visit it again, this time with all options enabled
          let e'TypeAbs ← withIncDepth <| visit e'Type
          trace[Autogeneralize.abstractPattern] m!"⭐ Generating hypothesis {e'TypeAbs}"
          mkExprMVar e'TypeAbs -- mvar for generalized hypothesis
            -- (userName := mkAbstractedName n)
  visit e

end ReplacePatternWithMVars

/- Just like kabstract, except abstracts to mvars instead of bvars
  We use this to abstract the theorem TYPE...so we can re-specialize non-abstracted occurrences in the proof.
  -/
def abstractToOneMVar (thmType : Expr) (pattern : Expr) (occs : Occurrences) : MetaM Expr := do
  let userThmType ← kabstract thmType pattern (occs)

  let userMVar ←  mkFreshExprMVar (← inferType pattern)
  let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
  let userThmType := userThmType.instantiate1 annotatedMVar

  return userThmType

/-
  Just like kabstract, except abstracts to different variables instead of the same one
  We use this to abstract the theorem TYPE...so we can re-specialize non-abstracted occurrences in the proof.
-/
def abstractToDiffMVars (e : Expr) (p : Expr) (occs : Occurrences) : MetaM Expr := do
  let pType ← inferType p
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      | .app f a          => return e.updateApp! (← visit f) (← visit a)
      | .mdata _ b        => return e.updateMData! (← visit b)
      | .proj _ _ b       => return e.updateProj! (← visit b)
      | .letE _ t v b nd  => return e.updateLet! (← visit t) (← visit v) (← visit b) nd
      | .lam _ d b _      => return e.updateLambdaE! (← visit d) (← visit b)
      | .forallE _ d b _  => return e.updateForallE! (← visit d) (← visit b)
      | e                 => return e
    if e.hasLooseBVars then
      visitChildren ()
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let i ← get
        set (i+1)
        if occs.contains i then
          let userMVar ← mkFreshExprMVar pType
          let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
          return annotatedMVar
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  visit e |>.run' 1
