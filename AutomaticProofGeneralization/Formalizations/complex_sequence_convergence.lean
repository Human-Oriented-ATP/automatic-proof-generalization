import Mathlib
import AutomaticProofGeneralization.AutoGeneralizeTactic

open Filter

-- `0` is less than or equal to `2`
-- HACK: this is needed for the `autogeneralize` algorithm to detect and generalize the `2` in the proof correctly
lemma zero_le_two_ℝ : (0 : ℝ) ≤ (2 : ℝ) := zero_le_two

theorem complex_sum_convergence
  -- `z` is a sequence of complex numbers
  (z : ℕ → ℂ)
  -- eventually, the sequence `z` decays by half at each step
  (h : ∃ N, ∀ n ≥ N, ‖z (n+1)‖ ≤ ‖z n‖ / (2 : ℝ))
  -- To prove: `z` is summable
  : Summable z := by
  -- obtain the number `N` after which the sequence starts decaying by half at each step
  obtain ⟨N, hN⟩ := h
  -- the "tail" of the sequence `z` starting from `N`, i,e., the sequence `z_N, z_{N+1}, z_{N+2}, ...`
  let z' : ℕ → ℂ := fun n ↦ z (n + N)
  -- it is sufficient (and equivalent) to show the summability of the tail sequence `z'`
  rw [← summable_nat_add_iff N]
  show Summable z'
  -- rephrasing the condition about the sequence decaying by half at each step in terms of `z'`
  let h' : ∀ b : ℕ, ‖z' (b + 1)‖ ≤ ‖z' b‖ / 2 := by
    intro b
    specialize hN (b + N) (by simp)
    unfold z'
    rwa [Nat.add_right_comm]
  -- to show that a sequence is summable, it suffices to show that it's a Cauchy sequence
  rw [@summable_iff_cauchySeq_finset]
  -- the hypothesis `h` implies that the sequence decays exponentially by a factor of `2` after a point
  let h' : ∀ m : ℕ, ‖z' m‖ ≤ ‖z' 0‖ / (2 : ℝ)^m := by
    intro m
    induction m with
    | zero => rw [npow_zero, div_one]
    | succ m ih =>
      calc  ‖z' (m + 1)‖
        _ ≤ ‖z' m‖ / 2           := by apply h'
        _ ≤ (‖z' 0‖ / 2^m) / 2   := by exact div_le_div_of_nonneg_right ih zero_le_two_ℝ
        _ = ‖z' 0‖ / 2 ^ (m + 1) := by rw [@div_div, @npow_add, @npow_one]
  -- this function is an upper bound for the norms of the sequence
  -- it is sufficient to show the summability of this sequence
  let z'Bound : ℕ → ℝ := fun n ↦ ‖z' 0‖ / 2 ^ n
  -- the hypothesis `h'` shows that `‖z' i‖ ≤ z'Bound i` for all `i : ℕ`
  -- it suffices to show that `z'Bound` is summable
  refine cauchySeq_finset_of_norm_bounded z'Bound ?z'BoundSummable h'
  -- `z'Bound` is pointwise equal to `fun n => ‖z 0‖ * (1 / 2) ^ n`
  -- the specific form of the second sequence allows
  apply Summable.congr (f := fun n => ‖z' 0‖ * (1 / 2) ^ n)
  swap
  · -- prove that `z'Bound` is equal to the other sequence pointwise
    intro _
    unfold z'Bound
    rw [@div_pow, @one_pow, @mul_one_div]
  · -- the multiplicative constant `‖z' 0‖` can be ignored
    apply Summable.mul_left
    -- the sequence `(1 / 2) ^ n` is summable
    exact summable_geometric_two

/--
info: Successfully generalized ⏎
  complex_sum_convergence ⏎
to ⏎
  complex_sum_convergence.Gen : ∀ (m : ℝ),
  0 ≤ m → (Summable fun n => (1 / m) ^ n) → ∀ (z : ℕ → ℂ), (∃ N, ∀ n ≥ N, ‖z (n + 1)‖ ≤ ‖z n‖ / m) → Summable z ⏎
by abstracting 2.
-/
#guard_msgs in
example : True := by
  autogeneralize (2 : ℝ) as m in complex_sum_convergence
  trivial
