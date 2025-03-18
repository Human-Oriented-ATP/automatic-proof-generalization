import Lean
open Lean Elab Tactic Meta Term Command

/-- Run Lean's built-in "simp" tactic -/
def performSimp (genThmType : Expr ) (genThmProof : Expr) : MetaM (Expr × Expr) := do
  let (result, _) ← Lean.Meta.simp genThmType (← Simp.mkContext)
  let genThmTypeSimp := result.expr
  let genThmProofSimp ← mkAppM `Eq.mpr #[← result.getProof, genThmProof]
  return (genThmTypeSimp, genThmProofSimp)


/-- Unifies metavariables (which are hypotheses) when possible.  -/
def removeRepeatingHypotheses (genThmProof : Expr) : MetaM Expr := do
  let hyps ← getMVars genThmProof
  for hyp₁ in hyps do
    for hyp₂ in hyps do
      -- performs unificiation on propositions
      if (← isProp <| ← hyp₁.getType) then do
        -- `discard` ignores the result of its argument (but retains modifications to the state)
        -- `isDefEq` automatically rejects cases where the meta-variables have different types or have conflicting assignments
        discard <| isDefEq (.mvar hyp₁) (.mvar hyp₂)

  return genThmProof
