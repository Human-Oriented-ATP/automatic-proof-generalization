import Lean
import Mathlib.Data.Fintype.BigOperators

theorem union_of_finsets
  {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α)
  (hA : A.card = 2) (hB : B.card = 2) : (A ∪ B).card ≤ 4 :=
by
  apply hA ▸ hB ▸ Finset.card_union_add_card_inter A B ▸ Nat.le_add_right _ _
