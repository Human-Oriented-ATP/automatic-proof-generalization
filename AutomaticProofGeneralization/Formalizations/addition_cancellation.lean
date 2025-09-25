import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem cancellation : ∀ a b c : ℤ, a + b = a + c → b = c :=
by
  intros a b c h
  replace h : -a + (a + b) = -a + (a + c) := by
    rw [h]
  rw [← add_assoc, ← add_assoc, Int.add_left_neg, zero_add, zero_add] at h
  exact h
