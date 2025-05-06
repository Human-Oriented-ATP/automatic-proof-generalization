import Mathlib
import LeanAideTools

-- #theorem "Let (z_n)_1^infty be a sequence of complex numbers. Suppose that there exists N such that for all n >= N, |z_n| <= |z_{n-1}|/2. Then the sum ∑{n=1}^infty z_n converges."
open Filter

#check @cauchySeq_finset_iff_nat_tsum_vanishing
#check @cauchySeq_finset_iff_vanishing_norm
#check @eventually_atTop
#check @cauchySeq_finset_of_summable_norm

#check Summable
#check Finset.range
-- #check Finset.map'
#check List.range

#check Summable.congr_atTop -- TODO: use this for a WLOG argument
#check Summable.mul_left

theorem complex_sum_convergence (z : ℕ → ℂ)
  (h : ∀ᶠ n in atTop, ‖z (n+1)‖ ≤ ‖z n‖ / 2)
    : Summable z := by
  rw [@summable_iff_cauchySeq_finset]
  rw [@eventually_atTop] at h
  rcases h with ⟨N, hN⟩
  have hN : ∀ m : ℕ, ∀ a ≥ N, ‖z (a + m)‖ ≤ ‖z a‖ / 2^m := by
    intro m a ha
    induction m with
    | zero => simp
    | succ m ih =>
      calc  ‖z (a + (m + 1))‖
          = ‖z ((a + m) + 1)‖   := by rw [add_assoc]
        _ ≤ ‖z (a + m)‖ / 2     := by apply hN; linarith only [ha]
        _ ≤ (‖z a‖ / 2^m) / 2   := by gcongr
        _ = ‖z a‖ / 2 ^ (m + 1) := by ring
  let zBound : ℕ → ℝ :=
    if hN_zero : N = 0 then
      (‖z 0‖ / 2 ^ ·)
    else fun n =>
      if n < N then
        -- the maximum of {‖z i‖ | 0 ≤ i < N}
        let normsUptoN := (List.range N).map (‖z ·‖)
        normsUptoN.maximum_of_length_pos (by
          have hnormsUptoN_length : normsUptoN.length = N := by
            simp only [List.length_map, List.length_range, normsUptoN]
          rw [hnormsUptoN_length]
          positivity)
      else
        ‖z N‖ / 2 ^ (n - N)
  apply cauchySeq_finset_of_norm_bounded zBound
  swap
  · intro i
    unfold zBound
    by_cases hN_zero : N = 0
    · subst hN_zero
      specialize hN i 0 (le_refl _)
      simp_all
    · simp [hN_zero]
      by_cases hN_lt : i < N
      · simp only [hN_lt, ↓reduceIte, List.le_maximum_of_length_pos_iff]
        refine List.le_maximum_of_mem' ?_
        refine List.mem_map_of_mem (fun x => ‖z x‖) ?_
        exact List.mem_range.mpr hN_lt
      · simp only [hN_lt, ↓reduceIte]
        specialize hN (i - N) N (le_refl _)
        rwa [@add_tsub_cancel_iff_le.mpr _] at hN
        linarith only [hN_lt]
  · unfold zBound
    by_cases hN_zero : N = 0
    · subst hN_zero
      simp only [↓reduceDIte]
      apply Summable.congr (f := fun n => ‖z 0‖ * (1 / 2) ^ n)
      swap
      · intro x
        ring_nf
      apply Summable.mul_left
      exact summable_geometric_two
    · sorry
