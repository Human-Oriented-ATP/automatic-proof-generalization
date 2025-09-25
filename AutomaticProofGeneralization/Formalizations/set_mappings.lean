import Lean
import Mathlib.Data.Fintype.BigOperators

theorem fun_set
  {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] :
  Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 :=
by
  intros α_card β_card
  rw [Fintype.card_pi, Finset.prod_const]
  congr
