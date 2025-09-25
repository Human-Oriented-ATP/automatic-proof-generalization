import Lean
import Mathlib.Data.Real.Irrational
open Real

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
IRRATIONALITY OF SQUARE ROOTS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
lemma prime_seventeen : Nat.Prime 17 := by decide

theorem irrat_def (n: ℕ) : (¬ ∃ a b : ℕ, Nat.gcd a b = 1 ∧ a*a = (n: ℕ) * b*b ) → Irrational (Real.sqrt n) := by
  contrapose
  simp
  intros irr
  unfold Irrational at irr
  simp at irr
  obtain ⟨x, irr⟩ := irr
  have x_pos : 0 ≤ (x:ℝ) := by
    have sqrt_pos := Real.sqrt_nonneg (n: ℝ)
    rw [← irr] at sqrt_pos
    apply sqrt_pos
  have n_pos : 0 ≤ (n:ℝ) := by
    exact Nat.cast_nonneg n
  have x_sq : x*x=n := by
    symm
    apply_mod_cast (Real.sqrt_eq_iff_mul_self_eq n_pos x_pos).mp (irr.symm)
  norm_num at x_pos
  have x_num_pos := (@Rat.num_nonneg x).mpr x_pos
  clear x_pos
  use Int.natAbs x.num
  use x.den
  constructor
  apply x.reduced
  rw [Rat.eq_iff_mul_eq_mul] at x_sq
  simp at x_sq

  rw [Rat.mul_self_num] at x_sq
  rw [Rat.mul_self_den] at x_sq

  have num_abs_eq_num : x.num = Int.natAbs x.num := Int.eq_natAbs_of_zero_le x_num_pos
  rw [num_abs_eq_num] at x_sq; clear num_abs_eq_num x_num_pos
  rw [mul_assoc n x.den x.den]
  apply_mod_cast x_sq

theorem irrat_sqrt : Irrational (√17) := by
  apply irrat_def
  intros h
  obtain ⟨a, b, ⟨copr, h⟩⟩ := h

  -- Show 17 ∣ a
  have a_div : 17 ∣ a := by
    have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp
      (by
        apply (Iff.mpr dvd_iff_exists_eq_mul_right)
        use (b*b)
        rw [← mul_assoc]
        rw [h]
      : 17 ∣ a*a)
    cases c
    case inl h₁ => assumption
    case inr h₂ => assumption

  -- a = 17 * k for some k
  have a_is_pk : ∃ k, a = 17 * k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div

  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  replace h := Eq.symm h
  rw [mul_assoc] at h
  rw [mul_assoc] at h
  rw [mul_comm 17 k] at h
  rw [mul_eq_mul_left_iff] at h
  rw [← mul_assoc k k 17] at h

  have nz := Nat.Prime.ne_zero prime_seventeen
  cases h with
  | inl =>
      -- Show 17 ∣ b
      have b_div : 17 ∣ b := by
        have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp
          (by
            apply (Iff.mpr dvd_iff_exists_eq_mul_left)
            use (k*k)
          )
        cases c
        case inl h₁ => assumption
        case inr h₂ => assumption

      -- 17 ∣ gcd a b
      have p_dvd_gcd : 17 ∣ Nat.gcd a b := by
        apply Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩

      clear a_div b_div
      rw [copr] at p_dvd_gcd
      apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd
  | inr =>
      apply nz
      assumption

theorem irrat_sum_sqrt : Irrational (sqrt (17:ℕ) + 17) := by
  apply Irrational.add_nat
  apply irrat_def
  intros h
  obtain ⟨a, b, ⟨copr, h⟩⟩ := h

  -- Show 17 ∣ a
  have a_div : 17 ∣ a := by
    have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp
      (by
        apply (Iff.mpr dvd_iff_exists_eq_mul_right)
        use (b*b)
        rw [← mul_assoc]
        rw [h]
      : 17 ∣ a*a)
    cases c
    case inl h₁ => assumption
    case inr h₂ => assumption

  -- a = 17 * k for some k
  have a_is_pk : ∃ k, a = 17 * k := by
    apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div

  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  replace h := Eq.symm h
  rw [mul_assoc] at h
  rw [mul_assoc] at h
  rw [mul_comm 17 k] at h
  rw [mul_eq_mul_left_iff] at h
  rw [← mul_assoc k k 17] at h

  have nz := Nat.Prime.ne_zero prime_seventeen
  cases h with
  | inl =>
      -- Show 17 ∣ b
      have b_div : 17 ∣ b := by
        have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp
          (by
            apply (Iff.mpr dvd_iff_exists_eq_mul_left)
            use (k*k)
          )
        cases c
        case inl h₁ => assumption
        case inr h₂ => assumption

      -- 17 ∣ gcd a b
      have p_dvd_gcd : 17 ∣ Nat.gcd a b := by
        apply Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩

      clear a_div b_div
      rw [copr] at p_dvd_gcd
      apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd
  | inr =>
      apply nz
      assumption
