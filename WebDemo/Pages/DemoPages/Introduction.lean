import VersoBlog
import AutomaticProofGeneralization.AutoGeneralizeTactic
import Mathlib.Data.Real.Irrational
-- import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts

open Verso Genre Blog

#doc (Page) "Introduction" =>

We present an algorithm that takes as its input a theorem, a proof of the theorem, and some aspect of the theorem that can potentially be generalized, and outputs a correct generalization of the theorem and proof.

These demos accompany our paper "Automatically Generalizing Proofs and Statements" submitted to ITP 2025.

# A First Example

Consider the following theorem and proof that the square root of 17 is irrational.

```leanInit demo
```

For example, given the theorem & proof that √2 is irrational….
```lean demo
theorem irrat_sqrt : Irrational (√17) := sorry
  -- by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 17 ∣ a := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 17 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 17 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 17 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 17] at h; have := Nat.Prime.ne_zero prime_seventeen; cases h with | inl => have b_div : 17 ∣ b := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 17 ∣ Nat.gcd a b := by {apply Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd | inr => apply this; assumption}

```

If our algorithm is presented with the above theorem and proof, formalized in Lean, and asked to generalize the number 17 by replacing it with an unknown natural number $`n`, it will determine that the only property it used of the number 17 was that it was prime, so its output will be the theorem that if $`n` is prime, then $`\sqrt n`is irrational, together with a correct proof of that theorem.
