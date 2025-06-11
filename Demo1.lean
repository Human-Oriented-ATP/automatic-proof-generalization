/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Demos of proof generalization tactic in Lean
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts

open Autogeneralize
open Real

set_option pp.showLetValues false
set_option linter.unusedVariables false


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Generalization of the proof that √17 is irrational
to the proof that the square root of any prime is irrational.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example : ∀ (p : ℕ), Nat.Prime p → Irrational √p := by

  /- Start with the theorem that √17 is irrational. -/
  let irrat_sqrt : Irrational (√17) := by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 17 ∣ a := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 17 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 17 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 17 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 17] at h; have := Nat.Prime.ne_zero prime_seventeen; cases h with | inl => have b_div : 17 ∣ b := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 17 ∣ Nat.gcd a b := by {apply Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd | inr => apply this; assumption}

  /- Find the proof-based generalization of 17 to any prime, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sqrt

  assumption
