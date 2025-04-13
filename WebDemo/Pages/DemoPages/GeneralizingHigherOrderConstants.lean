import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.bezout_identity
import VersoBlog

open Verso Genre Blog

open Classical

#doc (Page) "Generalizing Higher-Order Constants" =>

```leanInit generalizingHigherOrderConstants
```

```lean generalizingHigherOrderConstants show:=false
set_option pp.showLetValues false
```

Since both Pons's algorithm and our extension assume type-theoretic foundations, generalizing constants like $`\mathbb{R}` or $`*` (multiplication) works just as well as generalizing numerical constants.

# Generalizing a proof of left-cancellation in the integers

As an example, consider the following result proving left-cancellation on the integers from more basic axioms.

```lean generalizingHigherOrderConstants
/-- For any three integers a,b and c, if a+b=a+c, then b=c. -/
theorem Int.left_cancellation (a b c : ℤ) (h : a + b = a + c) : b = c := by
  replace h : -a + (a + b) = -a + (a + c) := by rw [h]
  rwa [← Int.add_assoc, Int.add_left_neg, ← Int.add_assoc, Int.add_left_neg, Int.zero_add, Int.zero_add] at h
```

This can be proved by adding $`-a` to both sides (on the left), applying associativity, noting that $`a+-a=0`, and using the fact that $`0` is an additive identity.

Each step of the argument works just as well in an arbitrary semigroup with an identity and left inverse, so in fact the proof gives the following result.

```lean generalizingHigherOrderConstants
example : ∀ (T : Type)        -- If you have an arbitrary set
  [inverse : Neg T]           -- with a symbol representing the inverse,
  (e : T)                     -- and a symbol representing the identity,
  (f : T → T → T),            -- and a binary operation
  (∀ (a : T), f e a = a) →    -- s.t. the identity element is left-neutral w.r.t. the operation
  (∀ (a : T), f (-a) a = e) → -- and every element has a left inverse under the operation
  (∀ (a b c : T), f (f a b) c = f a (f b c)) → -- and the operation is associative,
  ∀ (a b c : T), f a b = f a c → b = c -- then the operation is left-cancellative.
:= by
  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize_basic (Add.add) in Int.left_cancellation
  autogeneralize (0) as e in Int.left_cancellation.Gen
  autogeneralize (ℤ) in Int.left_cancellation.Gen.Gen

  assumption
```

What the algorithm has done here by generalizing the constants $`+`, $`0`, and $`\mathbb{Z}` is to show that the conclusion holds in a semigroup with an identity and left inverses. Importantly, the algorithm does not need to have prior knowledge of these more abstract concepts: it discovers the abstractions for itself.

# Generalizing Bézout's theorem from number theory

A more complicated example of this kind is provided by Bézout's theorem from elementary number theory. Our algorithm is capable of generalizing the non-numerical constant $`\mathbb{Z}` in a standard proof of this theorem, which states that the greatest common divisor of two integers $`x` and $`y` can always be expressed as a linear combination of $`x` and $`y` with integer coefficients.

```lean generalizingHigherOrderConstants
/- Bézout's identity states that for any two integers a and b, there exist integers x and y such that
  their greatest common divisor g can be expressed as a linear combination ax + by = g. -/
#check (bezout_identity : ∀ a b : ℤ, b ≠ 0 → ∃ x y, isGCD (x * a + y * b) a b)
```

Generalizing the integers in this proof produces a definition broadly similar to that of a Euclidean domain from ring theory, which, roughly speaking, means an integral domain with a measure of size that allows one to run the Euclidean algorithm and guarantees that it will terminate.

```lean generalizingHigherOrderConstants
example := by
  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize ℤ as R in bezout_identity
  assumption
```

More specifically, it produces, among other hypotheses, the following conditions under which the theorem holds for a set $`R`.
- The set has the appropriate additive and multiplicative structure (in particular, it must be a group under addition and multiplication must distribute over addition).
- The set comes equipped with a function $`R \to \mathbb{N}` (the "size function"), which is the generalization of the absolute value function on the integers.
- The only element in $`R` of size $`0` is the additive identity $`0`.
- There are functions $`q, r : R \times R \to R`, generalizations of the quotient and remainder, respectively, that satisfy the property $`a = q(a, b)\cdot b + r(a, b)` for elements $`a, b \in R`.
- Additionally, for any $`a, b \in R` such that $`b \neq 0`, the size of $`r(a, b)` is strictly less than the size of $`b`.
