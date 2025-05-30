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
