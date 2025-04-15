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

Since both our algorithm and [its predecessor](https://cedric.cnam.fr/~pons/PAPERS/types00.pdf) assume type-theoretic foundations, generalizing constants like $`\mathbb{ℤ}` (integers) or $`+` (addition) works just as well as generalizing numerical constants.

# Generalizing Integer Addition

As an example, consider the following result proving left-cancellation on the integers from more basic axioms.

$$`\textrm{For any } a,b,c \in ℤ, \textrm{ if } a+b=a+c, \textrm{ then } b=c.`

```lean generalizingHigherOrderConstants
theorem Int.left_cancellation
  (a b c : ℤ) (h : a + b = a + c) : b = c :=
by
  /- Add '-a' to both sides. -/
  replace h : -a + (a + b) = -a + (a + c) := by rw [h]

  /- Apply associativity and cancel. -/
  rwa [← Int.add_assoc, Int.add_left_neg, ← Int.add_assoc, Int.add_left_neg, Int.zero_add, Int.zero_add] at h
```

We prove it by adding $`-a` to both sides (on the left), applying associativity, noting that $`a+-a=0`, and using the fact that $`0` is an additive identity.

Our program will recognize that each step of the argument works just as well in an arbitrary semigroup with an identity and left inverse, so in fact the proof gives the following result.

$$`\textrm{Let } (G, \cdot) \textrm{ be a semigroup with an identity and left inverse.}\\
\textrm{For any } a,b,c \in G, \textrm{ if } a \cdot b=a \cdot c, \textrm{ then } b=c.`

```lean generalizingHigherOrderConstants
example : ∀ (G : Type)        -- If you have an arbitrary set
  [inverse : Neg G]           -- with a symbol representing the inverse,
  (e : G)                     -- and a symbol representing the identity,
  (f : G → G → G),            -- and a binary operation
  (∀ (a : G), f e a = a) →    -- s.t. the identity element is left-neutral w.r.t. the operation
  (∀ (a : G), f (-a) a = e) → -- and every element has a left inverse under the operation
  (∀ (a b c : G), f (f a b) c = f a (f b c)) → -- and the operation is associative,
  ∀ (a b c : G), f a b = f a c → b = c -- then the operation is left-cancellative.
:= by
  /- Generalize addition to an arbitrary binary operation. -/
  autogeneralize_basic (Add.add) in Int.left_cancellation
  /- Generalize 0 to an arbitrary identity element. -/
  autogeneralize (0) as e in Int.left_cancellation.Gen
  /- Generalize ℤ to an arbitrary semigroup. -/
  autogeneralize (ℤ) as G in Int.left_cancellation.Gen.Gen

  /- Use the generalization to close the goal. -/
  assumption
```

Thus, by generalizing the constants $`+`, $`0`, and $`\mathbb{Z}`, the algorithm has found that the conclusion holds in a semigroup with an identity and left inverses. Importantly, the algorithm does not need to have prior knowledge of these more abstract concepts: it discovers the abstractions for itself.

# Generalizing ℤ in Bézout's Identity

A more complicated example of this kind is provided by Bézout's identity from elementary number theory. Our algorithm is capable of generalizing the non-numerical constant $`\mathbb{Z}` in a standard proof of this theorem.

$$`\textrm{Let } x,y \in \mathbb{Z}, \textrm{ where } y \neq 0.\\
\textrm{There exist } h,k \in \mathbb{Z} \textrm{ such that } hx + ky = \gcd(x,y).`

```lean generalizingHigherOrderConstants
#check (bezout_identity : ∀ x y : ℤ, y ≠ 0 → ∃ h k, isGCD (h * x + k * y) x y)
```

Generalizing the integers in this proof produces a definition broadly similar to that of a Euclidean domain from ring theory, i.e. roughly speaking, an integral domain with a measure of size that allows one to run the Euclidean algorithm and guarantees that it will terminate.

```lean generalizingHigherOrderConstants
example := by
  /- Generalize ℤ in Bezout's identity -/
  autogeneralize ℤ as R in bezout_identity -- <- click to see the generalization

  assumption
```

That is, the program identifies, among others, the following conditions under which the theorem holds for an arbitrary set $`R`.
- The set has the appropriate additive and multiplicative structure (in particular, $`R` must be a group under addition, and multiplication must distribute over addition).
- The set comes equipped with a function $`R \to \mathbb{N}` (the "size function"), which is the generalization of the absolute value function on the integers.
- The only element in $`R` of size $`0` is the additive identity $`0`.
- There are functions $`q, r : R \times R \to R`, generalizations of the quotient and remainder, respectively, that satisfy the property $`a = q(a, b)\cdot b + r(a, b)` for elements $`a, b \in R`.
- For any $`a, b \in R` such that $`b \neq 0`, the size of $`r(a, b)` is strictly less than the size of $`b`.
