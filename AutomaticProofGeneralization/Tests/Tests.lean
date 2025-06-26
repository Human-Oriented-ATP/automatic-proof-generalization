/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Tests to validate more subtle behavior of the algorithm.
These are tests that are too technical to be demos.
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import AutomaticProofGeneralization.AutoGeneralizeTactic
import Mathlib.Tactic

/- Test that autogeneralize can generalize 0 even though it relies on typeclasses. -/
theorem exists_left_id : ∀ (x : ℤ), ∃ (y : ℤ), y + x = x := by
  intro x
  exists (0 : ℤ)
  exact zero_add x

example :
  ∀ (T : Type) [Add T] (_ : {n : ℕ} → OfNat T n), (∀ (a : T), 0 + a = a) → ∀ (x : T), ∃ y, y + x = x :=
by
  autogeneralize ℤ in exists_left_id
  assumption

/- Test that autogeneralize can generalize the concatenate function. -/
theorem reverse_concat (xs : List Int) : (0 :: xs).reverse = xs.reverse.concat 0 :=
  List.reverse_cons' 0 xs

example : True := by
  autogeneralize List.concat in reverse_concat
  trivial

/- Test that autogeneralize can generalize the 2 in a modular arithmetic problem. -/
theorem split_squares (x y : Int) : (x + y)^2 ≡ x^2 + y^2 [ZMOD 2] := by
  have binom_exp : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := add_sq x y
  have : (x + y)^2 = x^2 + y^2 + 2 * x * y := by
    rw [binom_exp, add_assoc, add_comm (2 * x * y), add_assoc]
  rw [this, mul_assoc]
  exact Int.modEq_add_fac_self

set_option maxHeartbeats 2500000 in
example : True := by
  autogeneralize 2 in split_squares
  trivial

/- Test that autogeneralize can generalize proofs involving the 'calc' tactic. -/
example : ∀ (n m : ℕ) {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α),
  A.card = n → B.card = m → (A ∪ B).card ≤ n+m := by

  let union_of_finsets
      {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2) :
      (A ∪ B).card ≤ 4 := by calc
    (A ∪ B).card ≤ (A ∪ B).card + (A ∩ B).card := Nat.le_add_right _ _
    _ = A.card + B.card := Finset.card_union_add_card_inter _ _
    _ = 2 + B.card := by rw [hA]
    _ = 2 + 2 := by rw [hB]
    _ = 4 := rfl

  autogeneralize (2:ℕ) in union_of_finsets

  assumption

/- Test that autogeneralize can generalize parts of proofs not explicitly encoded in lemmas.  -/
lemma one_lt_three_pow {n : ℕ} (hn : n ≠ 0) : 1 < 3 ^ n := by
  have hpow_lt : 1 ^ n < 3 ^ n := Nat.pow_lt_pow_left (a := 1) (b := 3) ?_ hn
  rwa [one_pow] at hpow_lt
  · exact Nat.one_lt_succ_succ 1 -- 1 < 3

example : ∀ m, 1 < m → ∀ n, n ≠ 0 → 1 < m ^ n := by
  autogeneralize (3 : ℕ) as m in one_lt_three_pow
  assumption
