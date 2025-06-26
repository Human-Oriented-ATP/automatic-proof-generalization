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
