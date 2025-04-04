import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts
import Mathlib.Data.Fintype.Pi
import VersoBlog

set_option pp.showLetValues false

open Verso Genre Blog

#doc (Page) "Handling Repeated Constants" =>

```leanInit generalizingMultipleOccurrences
```

Often, a proof will contain the same constant multiple times.  When we generalize, the proof should tell us whether these instances of the constant must necessarily be equal for the proof to go through, or whether each instance plays a different role in the proof.

# Generalizing Instances Separately


So, in a proof where a constant appears multiple times, the algorithm can determine when to generalize each occurrence separately.

Consider the following proof that $`17 + \sqrt{17}` is irrational.

```lean generalizingMultipleOccurrences
theorem irrat_sum:
  Irrational (17 + Real.sqrt (17:ℕ)) :=
by
  /- It suffices to show that `√17` is irrational,
     since a natural number plus an irrational is irrational. -/
  apply Irrational.nat_add

  /- The rest of the proof shows that √17 is irrational. -/
  apply irrat_def
  rintro ⟨a, b, ⟨copr, h⟩⟩; have a_div : 17 ∣ a := by {have c : 17 ∣ a * a := by {rw [h, mul_assoc]; exact Nat.dvd_mul_right _ _}; rw [Nat.Prime.dvd_mul prime_seventeen] at c; cases c <;> assumption}
  have a_is_pk : ∃ k, a = 17 * k := Iff.mp dvd_iff_exists_eq_mul_right a_div
  obtain ⟨k, hk⟩ := a_is_pk; rw [hk] at h; symm at h; rw [mul_assoc, mul_assoc, mul_comm 17 k, mul_eq_mul_left_iff, ← mul_assoc k k 17] at h; simp only [Nat.Prime.ne_zero prime_seventeen, or_false] at h
  have b_div : 17 ∣ b := by {have c : 17 ∣ b * b := by {rw [h]; exact Nat.dvd_mul_left 17 (k * k)}; rw [Nat.Prime.dvd_mul prime_seventeen] at c; cases c <;> assumption}
  have p_dvd_gcd : 17 ∣ Nat.gcd a b := Iff.mpr Nat.dvd_gcd_iff ⟨a_div, b_div⟩; clear a_div b_div; rw [copr] at p_dvd_gcd; apply Nat.Prime.not_dvd_one prime_seventeen p_dvd_gcd
```

We would not want the generalization to place the primality assumption on both occurences of $`17`, yielding the overly-specific generalization that $`p+\sqrt{p}` is irrational for any prime $`p`.

Happily, our algorithm yields the stronger generalization that $`n+\sqrt{p}` is irrational for any natural number $`n` and prime $`p`.

```lean generalizingMultipleOccurrences
theorem irrat_sum_generalized:
  ∀ (p : ℕ), Nat.Prime p → ∀ (n : ℕ), Irrational (n + √p) :=
by
  /- Generalize the `17` in the proof,
     then add the generalization `irrat_sum.Gen` as a hypothesis. -/
  autogeneralize (17:ℕ) in irrat_sum

  /- Use the generalization to close the goal.-/
  assumption
```


We can also choose to selectively generalize a particular occurrence of a constant. Below, we only generalize the occurrence of $`17` under the square root, yielding the generalization that $`17+\sqrt{p}` is irrational for any prime $`p`.

```lean generalizingMultipleOccurrences
theorem irrat_sum_semigeneralized:
  ∀ (p : ℕ), Nat.Prime p → Irrational (17 + √p) :=
by
  /- Selectively generalize the occurrence of `17` under the square root,
    then add the generalization `irrat_sum.Gen` as a hypothesis. -/
  autogeneralize (17:ℕ) in irrat_sum at occurrences [1]

  /- Use the generalization to close the goal.-/
  assumption
```

# Generalizing Instances Together

If different occurrences of a constant play the same role in the proof, the program automatically detects this and generalizes them as the same constant.

For example, consider the following theorem which proves that the number of functions between two sets of size `3` is `3 ^ 3`.

```lean generalizingMultipleOccurrences
theorem fun_set
  {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
  (α_card : Fintype.card α = 3) (β_card : Fintype.card β = 3) :
  Fintype.card (α → β) = 3 ^ 3 :=
by
  rw [Fintype.card_pi, Finset.prod_const]; congr
```

Generalizing each of the four instances of $`3` to a different variable here would yield an incorrect statement. Rather, the cardinality of $`\alpha` is linked to the base of the exponent $`3^3`, and the cardinality of $`\beta` is linked to the power of the exponent $`3^3`. Generalizing all four instances of $`3` in this proof creates only two variables, one for each pair of linked occurrences.  The result is the generalization that if |α| = n and |β| = m, then the number of functions $`f : α → β` is $`m^n`.

```lean generalizingMultipleOccurrences
theorem fun_set_generalized :
  ∀ (n m : ℕ)
  {α β : Type} [Fintype α] [Fintype β] [DecidableEq α],
  Fintype.card α = n → Fintype.card β = m →
  Fintype.card (α → β) = m ^ n:=
by
  /- Generalize all occurrences of `3` in the proof,
     then add the generalization `fun_set.Gen` as a hypothesis. -/
  autogeneralize 3 in fun_set

  /- Use the generalization to close the goal.-/
  assumption
```

At a high level, we determine whether two occurrences of a constant play the same role in a proof by checking if the two metavariables they have been replaced with unify after consolidating the proof (for instance, by running typechecking to match up inferred statements in the proof with the expected ones).  For details on the technical implementation of this algorithm, please see the paper "Automatically Generalizing Proofs and Statements."
