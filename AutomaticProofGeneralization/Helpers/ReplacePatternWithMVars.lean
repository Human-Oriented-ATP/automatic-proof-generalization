import Lean
import AutomaticProofGeneralization.Helpers.Antiunification
import AutomaticProofGeneralization.Helpers.Metavariables
import AutomaticProofGeneralization.Helpers.Naming
import AutomaticProofGeneralization.Helpers.FunctionApplications

open Lean Elab Tactic Meta Term Command AntiUnify

initialize
  registerTraceClass `TypecheckingErrors

/--
Replaces all instances of `p` in `e` with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't look for instances of "p" in the types of constants, this does
  kabstract doesn't look under binders, but this creates LocalDecls so we can still look under binders
-/
partial def replacePatternWithMVars (e : Expr) (p : Expr) (lctx : LocalContext) (linsts : LocalInstances) : StateT (List Expr) MetaM Expr := do
  -- logInfo m!"We are replacing the pattern {p}:{← inferType p} with mvars."

  -- the "depth" here is not depth of expression, but how many constants / theorems / inference rules we have unfolded
  let rec visit (e : Expr) (depth : Nat := 0): StateT (List Expr) MetaM Expr := do
    let visitChildren : Unit →  StateT (List Expr) MetaM Expr := fun _ => do
      if e.hasLooseBVars then
        logInfo m!"Loose BVars detected on expression {e}"
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
      | .app f a         =>
                            let mut fAbs ← visit f depth -- the type
                            let expectedA ← extractArgType fAbs
                            let aAbs ← visit a depth
                            let inferredA ← inferType aAbs
                            if ← liftM <| withoutModifyingState <| isDefEq expectedA inferredA then
                              return e.updateApp! fAbs aAbs
                            else
                              trace[TypecheckingErrors] m!"Error in typechecking: aAbs was expected to have type \n\t{expectedA} \nbut has type \n\t{inferredA}"

                              -- the mismatch is probably caused because something else needs to be generalized
                              let (_result, problemTerms) ← getTermsToGeneralize expectedA inferredA
                              trace[TypecheckingErrors] m!"The mismatch can probably be fixed by generalizing the terms {problemTerms}"
                              modify fun terms ↦ (problemTerms.map Prod.snd ++ terms).eraseDups
                              return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b depth)
      | .proj _ _ b      => return e.updateProj! (← visit b depth)
      | .letE n t v b _ =>  let tAbs ← visit t depth
                            let vAbs ← visit v depth
                            -- ensure that the generalized value and type are still in sync
                            unless ← isDefEq tAbs (← inferType vAbs) do
                              throwError m!"Expected the type of {vAbs} in `let` statement to be {tAbs}, but got {← inferType vAbs}"
                            let updatedLet ← withLetDecl n tAbs vAbs (fun placeholder => do
                              let b := b.instantiate1 placeholder
                              let bAbs ← if (←  liftM <| withoutModifyingState (isDefEq tAbs t)) then
                                    visit b depth -- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"tAbs {tAbs} and t {t} are not defeq"
                                    return b
                              return ← mkLetFVars (usedLetOnly := false) #[placeholder] bAbs-- put the "n:tAbs" back in the expression itself instead of in an external fvar
                            )
                            return updatedLet
      | .lam n d b bi     =>
                              let dAbs ← visit d depth
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedLambda ← withLocalDecl n bi dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ←
                                  if (←  liftM <| withoutModifyingState (isDefEq dAbs d)) then
                                    visit b depth-- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"dAbs {dAbs} and d {d} are not defeq"
                                    return b
                                return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              if updatedLambda.hasLooseBVars then
                                logInfo m!"Loose BVars detected on expression {e}"
                              return updatedLambda
      | .forallE n d b bi =>
                              let dAbs ← visit d depth
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedForAll ← withLocalDecl n bi dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ← visit b depth  -- now it's safe to recurse on b (no loose bvars)
                                return ← mkForallFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              return updatedForAll
      -- when we encounter a theorem used in the proof
      -- check whether that theorem has the variable we're trying to generalize
      -- if it does, generalize the theorem accordingly, and make its proof an mvar.
      -- | .const n us      => let constType ← inferType (.const n us) -- this ensures that universe levels are instantiated correctly

      --                       if depth > 2 then return e

      --                       else
      --                           let genConstType ← visit constType (depth+1)  -- expr for generalized proof statment
      --                           -- if the const does have the pattern in its definition, it is a property we should generalize
      --                           if genConstType.hasExprMVar then
      --                             let m ← mkFreshExprMVarAt lctx linsts genConstType (kind := .synthetic) (userName := mkAbstractedName n)-- mvar for generalized proof
      --                             return m
      --                           -- otherwise, we don't need to expand the definition of the const
      --                           else return e
      | e                => return e

    -- if the expression "e" is the pattern you want to replace...
    let mctx ← getMCtx
    if !e.isMVar && (← isDefEq e p) then
      -- since the type of `p` may be slightly different each time depending on the context it's in, we infer its type each time
      let pType ← instantiateMVars =<< inferType p
      setMCtx mctx
      let m ← mkFreshExprMVarAt lctx linsts pType (userName := placeholderName) -- replace every occurrence of pattern with mvar
      return m
    -- otherwise, "e" might contain the pattern...
    else
      setMCtx mctx
      -- so that other matches are still possible.
      let e' ← visitChildren ()

      if depth > 2 then
        return e'
      else
        let e'Type ← inferType e'
        let e'TypeAbs ← visit e'Type (depth + 1)
        let ⟨_, mismatches⟩ ← antiUnify e'Type e'TypeAbs
        if mismatches.isEmpty then -- if the two expressions are essentially the same
          return e'
        else
          let m ← mkFreshExprMVarAt lctx linsts e'TypeAbs (kind := .synthetic)
            -- (userName := mkAbstractedName n)-- mvar for generalized proof
          return m

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
