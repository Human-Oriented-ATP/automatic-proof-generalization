import VersoBlog
import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts

open Verso Genre Blog

#doc (Page) "Introduction" =>

We present an algorithm that takes as its input a theorem, a proof of the theorem, and some aspect of the theorem that can potentially be generalized, and outputs a correct generalization of the theorem and proof.

These demos accompany our paper submitted to ITP 2025: "Automatically Generalizing Proofs and Statements" by Anshula Gandhi, Anand Rao Tadipatri, and Timothy Gowers.

# Generalizing the Irrationality of √17

Consider the following theorem and proof that √17 is irrational.

```leanInit introduction
```

```lean introduction
theorem irrat_sqrt :
  Irrational √17 :=
by
  /- If 17 is irrational, we should not be able to find coprime a and b such that a/b = √17.  That is, a^2 = 17 b^2. -/
  apply irrat_def

  /- It follows that 17 | a^2.  Since 17 is prime, 17 | a. -/
  rintro ⟨a, b, ⟨copr, h⟩⟩; have a_div : 17 ∣ a := by {have c : 17 ∣ a * a := by {rw [h, mul_assoc]; exact Nat.dvd_mul_right _ _}; rw [Nat.Prime.dvd_mul prime_seventeen] at c; cases c <;> assumption}

  /- So we can write a = 17k for some k. -/
  have a_is_pk : ∃ k, a = 17 * k := Iff.mp dvd_iff_exists_eq_mul_right a_div

  /- Plugging  means 17 k^2 = b^2. -/
  obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; symm at h; rw [mul_assoc, mul_assoc, mul_comm 17 k, mul_eq_mul_left_iff, ← mul_assoc k k 17] at h; simp only [Nat.Prime.ne_zero prime_seventeen, or_false] at h

  /- It follows that 17 | b^2.  Since 17 is prime, 17 | b. -/
  have b_div : 17 ∣ b := by {have c : 17 ∣ b * b := by {rw [h]; exact Nat.dvd_mul_left 17 (k * k)}; rw [Nat.Prime.dvd_mul prime_seventeen] at c; cases c <;> assumption}

  /- Now we have a contradiction -- a and b were supposed to be coprime, but 17 divides both. -/
  have p_dvd_gcd : 17 ∣ Nat.gcd a b := Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one prime_seventeen p_dvd_gcd
```

If our algorithm is presented with the above theorem and proof, formalized in Lean, and asked to generalize the number 17 by replacing it with an unknown natural number $`n`, it will determine that the only property it used of the number 17 was that it was prime, so its output will be the theorem that if $`n` is prime, then $`\sqrt n` is irrational, together with a correct proof of that theorem.

```lean introduction
theorem irrat_sqrt_generalized :
   ∀ (p : ℕ), Nat.Prime p → Irrational √p :=
by
  /- Generalize `17` in the proof,
     then add the generalization `irrat_sqrt.Gen` as a hypothesis. -/
  autogeneralize (17:ℕ) in irrat_sqrt

  /- Use the generalization to close the goal.-/
  assumption
```
