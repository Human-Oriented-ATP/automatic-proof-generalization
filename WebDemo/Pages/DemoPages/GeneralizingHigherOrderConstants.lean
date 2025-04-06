import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.bezout_identity
import VersoBlog

open Verso Genre Blog

open Classical

#doc (Page) "Generalizing Higher-Order Constants" =>

```leanInit generalizingHigherOrderConstants
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
/-- Bézout's identity states that for any two integers a and b, there exist integers x and y such that their greatest common divisor g can be expressed as a linear combination ax + by = g -/
theorem bezout_theorem : ∀ (x y : ℤ), y ≠ 0 → ∃ (h k : ℤ), isGCD (h * x + k * y) x y := by
  intros x y y_neq_0

  -- Consider the set A = {hx + ky | x,y ∈ ℤ}
  let A := {z : ℤ | ∃ h k : ℤ, z = h * x + k * y}

  have A_add : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A := by
    rintro a ⟨h, k, a_eq⟩ b ⟨h', k', b_eq⟩
    use (discharger := skip) (h + h'), (k + k')
    rw [a_eq, b_eq]
    rw [Int.add_assoc, Int.add_left_comm (k * y) _ _, ← Int.add_assoc, ← Int.add_mul, ← Int.add_mul]
  have A_mul : ∀ a ∈ A, ∀ z : ℤ, z * a ∈ A := by
    rintro a ⟨h, k, a_eq⟩ z
    use z * h, z * k
    rw [a_eq]
    rw [Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc]

  -- Consider the set B = {|z| | z ∈ A, |z| ≠ 0} of non-zero absolute values
  let B := (Int.natAbs '' A) \ {0}
  -- Show B is non-empty by constructing an element
  have hB_nonempty : ∃ b : ℕ, b ∈ B := by
    use (0*x + 1*y).natAbs
    change (0*x + 1*y).natAbs ∈ Int.natAbs '' A \ {0}
    rw [Set.mem_diff_singleton]
    constructor
    · apply Set.mem_image_of_mem Int.natAbs
      use (discharger := rfl) 0, 1
    · rwa [Int.zero_mul, Int.one_mul, Int.zero_add, @Ne.eq_def, Int.natAbs_eq_zero]
  -- By well-ordering principle on subsets of ℕ, B has a minimal element
  -- Call that minimal element "d"
  let Bmin : ℕ := Nat.find hB_nonempty
  have hBmin_spec : (∃ d ∈ A, d.natAbs = Bmin) ∧ Bmin ≠ 0 := Nat.find_spec hB_nonempty
  rcases hBmin_spec.1 with ⟨d, hd⟩
  have hdA := hd.1
  have hdAbs_eq_Bmin:= hd.2
  have hBmin_neq_0 := hBmin_spec.2
  have hdAbs_neq_0 : d.natAbs ≠ 0 := by rwa [← hdAbs_eq_Bmin] at hBmin_neq_0
  have hd_min : ∀ z ∈ A, z.natAbs = 0 ∨ d.natAbs ≤ z.natAbs := by
    intro z hz
    by_cases hzAbs : z.natAbs = 0
    · left
      assumption
    · right
      have hBmin_min := Nat.find_min' hB_nonempty (m := z.natAbs)
        ⟨Set.mem_image_of_mem Int.natAbs hz, hzAbs⟩
      rwa [hdAbs_eq_Bmin]

  have hd_div_A : ∀ a ∈ A, d ∣ a := by
    intro a ha_A
    -- By division algorithm, x = qd + r for some q,r with 0 ≤ r < d
    let q := a / d
    let r := a % d
    have a_eq_quotRem : a = q*d + r := Eq.symm (Int.ediv_add_emod' a d)
    have r_eq : r = (-q)*d + a := by
      rw [← neg_add_eq_iff_eq_add, Int.neg_mul_eq_neg_mul] at a_eq_quotRem
      symm; assumption
    have rAbs_lt_dAbs : r.natAbs < d.natAbs := by
      apply Int.emod_natAbs_lt_of_nonzero
      assumption
    have hr_A : r ∈ A := by
      rw [r_eq]
      apply A_add
      · apply A_mul; assumption
      · assumption
    by_cases hr_eq_0 : r.natAbs = (0 : ℕ)
    · rw [Int.natAbs_eq_zero] at hr_eq_0
      rw [a_eq_quotRem, hr_eq_0, Int.add_zero]
      exact Int.dvd_mul_left q d
    · have hd_min_r := hd_min r hr_A
      contrapose hd_min_r
      push_neg
      constructor <;> assumption

  have hxA : x ∈ A := by use 1, 0; simp only [Int.one_mul, Int.zero_mul, Int.add_zero]
  have d_dvd_x : d ∣ x := hd_div_A x hxA

  have hyA : y ∈ A := by use 0, 1; simp only [Int.zero_mul, Int.one_mul, Int.zero_add]
  have d_dvd_y : d ∣ y := hd_div_A y hyA

  obtain ⟨h, k, d_eq⟩ := hdA
  use (discharger := skip) h, k
  rw [isGCD]
  refine' ⟨_, _, _⟩
  · rwa [← d_eq]
  · rwa [← d_eq]
  · rintro c c_dvd_x c_dvd_y
    rw [Int.dvd_def] at c_dvd_x c_dvd_y ⊢
    rcases c_dvd_x with ⟨cx, hcx⟩
    rcases c_dvd_y with ⟨cy, hcy⟩
    use (h * cx + k * cy)
    rw [Int.mul_add, Int.mul_left_comm c h _, Int.mul_left_comm c k _, ← hcx, ← hcy]
```

Generalizing the integers in this proof produces a definition broadly similar to that of a Euclidean domain from ring theory, which, roughly speaking, means an integral domain with a measure of size that allows one to run the Euclidean algorithm and guarantees that it will terminate.

```lean generalizingHigherOrderConstants
example := by
  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize ℤ as R in bezout_theorem
  assumption
```

More specifically, it produces, among other hypotheses, the following conditions under which the theorem holds for a set $`R`.
- The set has the appropriate additive and multiplicative structure (in particular, it must be a group under addition and multiplication must distribute over addition).
- The set comes equipped with a function $`R \to \mathbb{N}` (the "size function"), which is the generalization of the absolute value function on the integers.
- The only element in $`R` of size $`0` is the additive identity $`0`.
- There are functions $`q, r : R \times R \to R`, generalizations of the quotient and remainder, respectively, that satisfy the property $`a = q(a, b)\cdot b + r(a, b)` for elements $`a, b \in R`.
- Additionally, for any $`a, b \in R` such that $`b \neq 0`, the size of $`r(a, b)` is strictly less than the size of $`b`.
