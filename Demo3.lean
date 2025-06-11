/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Demos of proof generalization tactic in Lean
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts

open Autogeneralize

set_option pp.showLetValues false
set_option autoImplicit false
set_option linter.unusedVariables false

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of robust generalization of _dependent_ uses of a constant.
Generalizing the _2_ below automatically generalizes the _4_.

Generalization of the proof that |A ∪ B| ≤ 4 when |A|=2 and |B|=2
to the proof that |A ∪ B| ≤ n+m when |A|=n and |B|=m
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example : ∀ (n m : ℕ) {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α),
  A.card = n → B.card = m → (A ∪ B).card ≤ n+m:= by

  /- Start with the theorem that |A ∪ B| ≤ 4 when |A|=2 and |B|=2. -/
  let union_of_finsets {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2) : (A ∪ B).card ≤ 4 := by apply hA ▸ hB ▸ Finset.card_union_add_card_inter A B ▸ Nat.le_add_right _ _

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (2:ℕ) in union_of_finsets

  assumption
