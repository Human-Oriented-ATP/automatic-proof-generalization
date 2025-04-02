import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts
import Mathlib.Data.Fintype.Pi
import VersoBlog

open Verso Genre Blog

#doc (Page) "Generalizing Multiple Occurrences" =>

```leanInit generalizingMultipleOccurrences
```

In a proof where a constant appears multiple times, the algorithm can generalize each occurrence separately.

Consider the following proof that $`\sqrt{17} + 17` is irrational.

```lean generalizingMultipleOccurrences
theorem irrat_sum_sqrt : Irrational (17 + Real.sqrt (17:ℕ)) := by
  -- it suffices to show that `√17` is irrational, since the result of adding a natural number to an irrational number is irrational.
  apply Irrational.nat_add
  -- the rest of the proof shows that √17 is irrational
  apply irrat_def
  rintro ⟨a, b, ⟨copr, h⟩⟩
  have a_div : 17 ∣ a := by
    have c : 17 ∣ a * a := by
      rw [h, mul_assoc]; exact Nat.dvd_mul_right _ _
    rw [Nat.Prime.dvd_mul prime_seventeen] at c
    cases c <;> assumption
  have a_is_pk : ∃ k, a = 17 * k := Iff.mp dvd_iff_exists_eq_mul_right a_div
  obtain ⟨k, hk⟩ := a_is_pk
  rw [hk] at h
  symm at h
  rw [mul_assoc, mul_assoc, mul_comm 17 k, mul_eq_mul_left_iff, ← mul_assoc k k 17] at h
  cases h with
  | inl h =>
    have b_div : 17 ∣ b := by
      have c : 17 ∣ b * b := by
        rw [h]; exact Nat.dvd_mul_left 17 (k * k)
      rw [Nat.Prime.dvd_mul prime_seventeen] at c
      cases c <;> assumption
    have p_dvd_gcd : 17 ∣ Nat.gcd a b := Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩
    clear a_div b_div
    rw [copr] at p_dvd_gcd
    apply Nat.Prime.not_dvd_one prime_seventeen p_dvd_gcd
  | inr h => apply Nat.Prime.ne_zero prime_seventeen; assumption
```

Generalizing this produces a proof that $`\sqrt{p}+n` is irrational for any prime $`p` and natural number $`n`.

```lean generalizingMultipleOccurrences
example: ∀ (p n : ℕ), Nat.Prime p → Irrational (n + √p) := by
  intros p n p_prime

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sum_sqrt

  exact irrat_sum_sqrt.Gen p p_prime n
```

In particular, it does not place the assumption of being prime on both occurences on $`17` in the statement, just on the relevant one.

We can also choose to selectively generalize a specified set of occurrences of a constant.

```lean generalizingMultipleOccurrences
example: ∀ (p : ℕ), Nat.Prime p → Irrational (17 + √p) := by
  intros p p_prime

  /- Selectively generalize the occurrence of `17` under the square root. -/
  autogeneralize (17:ℕ) in irrat_sum_sqrt at occurrences [1]

  exact irrat_sum_sqrt.Gen p p_prime
```

If different occurrences of a constant play the same role in the proof, the program automatically detects this and generalizes them as the same constant.

For example, consider the following theorem which proves that the number of functions between two sets of size `3` is `3 ^ 3`.

```lean generalizingMultipleOccurrences
/-- The number of functions between two sets of size `3` is `3 ^ 3`. -/
theorem fun_set {α β} [Fintype α] [Fintype β] [DecidableEq α]
    (α_card : Fintype.card α = 3) (β_card : Fintype.card β = 3) : Fintype.card (α → β) = 3 ^ 3 := by
  rw [Fintype.card_pi, Finset.prod_const]
  congr
```

Here, the cardinality of $`\alpha` is linked to the base of the exponent, and the cardinality of $`\beta` is linked to the power of the exponent. Generalizing $`3` in this proof creates two variables, one for each pair of linked occurrences.

```lean generalizingMultipleOccurrences
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] :
  ∀ (n m : ℕ), Fintype.card α = n → Fintype.card β = m → Fintype.card (α → β) = m ^ n :=
by
  intro n m

  let fun_set : Fintype.card α = 3 → Fintype.card β = 3 → Fintype.card (α → β) = 3 ^ 3 := by {intros α_card  β_card; rw [Fintype.card_pi, Finset.prod_const]; congr}

  /- Generalize all occurrences of `3` in the proof. -/
  autogeneralize 3 in fun_set

  exact fun_set.Gen n m
```
