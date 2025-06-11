/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Demos of proof generalization tactic in Lean
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.bezout_identity

open Autogeneralize

set_option pp.showLetValues false
set_option autoImplicit false
set_option linter.unusedVariables false


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of _generalizing non-numerical constants_ .

Generalization of Bezout's identity on the integers _ℤ_
to an arbitrary Euclidean domain.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

 /- Start with Bezout's identity in the integers -/
#check bezout_identity

example := by

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize ℤ in bezout_identity

  assumption
