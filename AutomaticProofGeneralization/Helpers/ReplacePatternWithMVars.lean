import Lean
import AutomaticProofGeneralization.Helpers.Antiunification
import AutomaticProofGeneralization.Helpers.Naming
import AutomaticProofGeneralization.Helpers.Metavariables
import AutomaticProofGeneralization.Helpers.FunctionApplications

open Lean Elab Tactic Meta Term Command AntiUnify

initialize
  registerTraceClass `TypecheckingErrors
  registerTraceClass `Autogeneralize.abstractPattern

local instance {α} : ExceptToEmoji Exception α where
  toEmoji
  | .error _ => crossEmoji
  | .ok _ => ""

structure ReplaceM.Context where
  lctx : LocalContext := {}
  localInstances : LocalInstances := {}
  depth : Nat := 0
  abstractHyps : Bool := true
  generalizeRelatedConstants : Bool := true
  cutOffDepth : Nat := 2

structure ReplaceM.State where
  mismatches : List Expr := []
  modified : Bool := false

abbrev ReplaceM := ReaderT ReplaceM.Context <| StateT ReplaceM.State MetaM

def ReplaceM.addConflictingTerms (terms : List Expr) : ReplaceM Unit := do
  modify fun σ => { σ with mismatches := (terms ++ σ.mismatches).eraseDups }

def ReplaceM.withReturnIfModified {α} (act : ReplaceM α) : ReplaceM (Option α) := do
  modify ({· with modified := false})
  let result ← act
  if (← get).modified then
    return some result
  else
    return none

def ReplaceM.mkExprMVar (type : Expr) (userName : Name := .anonymous) : ReplaceM Expr := do
  let ctx ← read
  let mvar ← mkFreshExprMVarAt ctx.lctx ctx.localInstances type (kind := .synthetic) (userName := userName)
  modify ({ · with modified := true })
  return mvar

def ReplaceM.withIncDepth {α} : ReplaceM α → ReplaceM α :=
  withReader fun ctx ↦ { ctx with depth := ctx.depth + 1 }

def ReplaceM.withoutAbstractingHypsOrGeneralizingConstants {α} : ReplaceM α → ReplaceM α :=
  withReader fun ctx ↦ { ctx with abstractHyps := false, generalizeRelatedConstants := false }

def ReplaceM.run {α} (m : ReplaceM α) : MetaM (α × ReplaceM.State) := do
  ReaderT.run m { lctx := ← getLCtx, localInstances := ← getLocalInstances } |>.run {}

def ReplaceM.run' {α} (m : ReplaceM α) : MetaM α := do
  ReaderT.run m { lctx := ← getLCtx, localInstances := ← getLocalInstances } |>.run' {}

open ReplaceM in
/--
Replaces all instances of `p` in `e` with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't look for instances of "p" in the types of constants, this does
  kabstract doesn't look under binders, but this creates LocalDecls so we can still look under binders
-/
partial def replacePatternWithMVars (e : Expr) (p : Expr) : ReplaceM Expr := do
  -- logInfo m!"We are replacing the pattern {p}:{← inferType p} with mvars."
  let pType ← withReducibleAndInstances <| reduce <| ← inferType p
  trace[Autogeneralize.abstractPattern] m!"Abstracting pattern {p} of type {pType}"
  -- the "depth" here is not depth of expression, but how many constants / theorems / inference rules we have unfolded
  let rec visit (e : Expr) : ReplaceM Expr := do
    let visitChildren : Unit → ReplaceM Expr := fun _ => do
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
      | .app f a         =>
                            let fAbs ← visit f -- the type
                            let aAbs ← visit a
                            if (← read).generalizeRelatedConstants then
                              let expectedA ← extractArgType fAbs
                              let inferredA ← inferType aAbs
                              unless ← liftM <| withoutModifyingState <| isDefEq expectedA inferredA do
                                trace[TypecheckingErrors] m!"Error in typechecking: aAbs was expected to have type \n\t{expectedA} \nbut has type \n\t{inferredA}"
                                -- the mismatch is probably caused because something else needs to be generalized
                                let (_result, problemTerms) ← getTermsToGeneralize expectedA inferredA
                                trace[TypecheckingErrors] m!"The mismatch can probably be fixed by generalizing the terms {problemTerms}"
                                ReplaceM.addConflictingTerms (problemTerms.map Prod.snd)
                            return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b)
      | .proj _ _ b      => return e.updateProj! (← visit b)
      | .letE n t v b _ =>  let tAbs ← visit t
                            let vAbs ← visit v
                            -- ensure that the generalized value and type are still in sync
                            unless ← isDefEq tAbs (← inferType vAbs) do
                              throwError m!"Expected the type of {vAbs} in `let` statement to be {tAbs}, but got {← inferType vAbs}"
                            let updatedLet ← withLetDecl n tAbs vAbs fun placeholder => do
                              let b := b.instantiate1 placeholder
                              let bAbs ← if (←  liftM <| withoutModifyingState <| isDefEq tAbs t) then
                                    visit b -- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"tAbs {tAbs} and t {t} are not defeq"
                                    pure b
                              return ← mkLetFVars (usedLetOnly := false) #[placeholder] bAbs-- put the "n:tAbs" back in the expression itself instead of in an external fvar

                            return updatedLet
      | .lam n d b bi     =>
                              let dAbs ← visit d
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedLambda ← withLocalDecl n bi dAbs fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ←
                                  if (←  liftM <| withoutModifyingState <| isDefEq dAbs d) then
                                    visit b-- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"dAbs {dAbs} and d {d} are not defeq"
                                    pure b
                                return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar

                              return updatedLambda
      | .forallE n d b bi =>
                              let dAbs ← visit d
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedForAll ← withLocalDecl n bi dAbs fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ← visit b  -- now it's safe to recurse on b (no loose bvars)
                                return ← mkForallFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar

                              return updatedForAll
      | e                =>
        return e

    withTraceNodeBefore `Autogeneralize.abstractPattern (pure m!"Visiting {e} at depth {(← read).depth}") do
      -- if the expression "e" is the pattern you want to replace...
      let mctx ← getMCtx
      if !e.isMVar && (← withReducibleAndInstances <| isDefEq e p) then -- (← liftM <| withoutModifyingState <| isDefEq e p) then
        -- since the type of `p` may be slightly different each time depending on the context it's in, we infer its type each time
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
          let e'Type ← inferType e'
          trace[Autogeneralize.abstractPattern] m!"🔍 Inspecting type {e'Type}"
          let some e'TypeAbs ←
            withReturnIfModified <| withIncDepth <| withoutAbstractingHypsOrGeneralizingConstants <|
              visit e'Type | return e'
            trace[Autogeneralize.abstractPattern] m!"⭐ Generating hypothesis {e'TypeAbs}"
          mkExprMVar e'TypeAbs
            -- (userName := mkAbstractedName n)-- mvar for generalized proof
  visit e

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
      | .app f a         => return e.updateApp! (← visit f ) (← visit a )
      | .mdata _ b       => return e.updateMData! (← visit b )
      | .proj _ _ b      => return e.updateProj! (← visit b )
      | .letE _ t v b _  => return e.updateLet! (← visit t ) (← visit v ) (← visit b )
      | .lam _ d b _     => return e.updateLambdaE! (← visit d ) (← visit b )
      | .forallE _ d b _ => return e.updateForallE! (← visit d ) (← visit b )
      | e                => return e
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
