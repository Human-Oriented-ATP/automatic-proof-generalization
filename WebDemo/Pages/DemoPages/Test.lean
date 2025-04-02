import VersoBlog
import AutomaticProofGeneralization.AutoGeneralizeTactic
import Mathlib.Data.Real.Irrational
-- import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts

open Verso Genre Blog

#doc (Page) "Test" =>

This is a tutorial on metaprogramming, or equivalently, writing tactics to help prove math theorems, in Lean 4.

That is, instead of focusing on writing a _formalized proof_ (programming), we focus on writing a _program that writes a formalized proof_ (metaprogramming).

# Looking Ahead to the Final Project

By the end of the tutorial, you will have built an "auto-generalization" Lean tactic.

The tactic takes an unnecessarily-weak theorem and turns it into a stronger theorem with an analogous proof (using an algorithm from the paper [Generalization in Type Theory Based Proof Assistants](http://cedric.cnam.fr/~pons/PAPERS/types00.pdf) by Oliver Pons).

```leanInit demo
```

For example, given the theorem & proof that √2 is irrational….
```lean demo
theorem irrat_sqrt : Irrational (√17) :=
  by {apply irrat_def; intros h; obtain ⟨a, b, ⟨copr, h⟩⟩ := h; have a_div : 17 ∣ a := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_right); use (b*b); rw [← mul_assoc]; rw [h];): 17 ∣ a*a); cases c; assumption; assumption}; have a_is_pk : ∃ k, a = 17 * k := by {apply (Iff.mp dvd_iff_exists_eq_mul_right) a_div}; obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; replace h := Eq.symm h; rw [mul_assoc] at h; rw [mul_assoc] at h; rw [mul_comm 17 k] at h; rw [mul_eq_mul_left_iff] at h; rw [← mul_assoc k k 17] at h; have := Nat.Prime.ne_zero prime_seventeen; cases h with | inl => have b_div : 17 ∣ b := by {have c := (Nat.Prime.dvd_mul (prime_seventeen)).mp ((by apply (Iff.mpr dvd_iff_exists_eq_mul_left); use (k*k))); cases c; assumption; assumption}; have p_dvd_gcd : 17 ∣ Nat.gcd a b := by {apply Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩}; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one (prime_seventeen) p_dvd_gcd | inr => apply this; assumption}

```
