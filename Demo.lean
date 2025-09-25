/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Demos of proof generalization tactic in Lean
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/
import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts
import AutomaticProofGeneralization.Formalizations.set_mappings
import AutomaticProofGeneralization.Formalizations.finset_union
import AutomaticProofGeneralization.Formalizations.impossible_graphs
import AutomaticProofGeneralization.Formalizations.addition_cancellation
import AutomaticProofGeneralization.Formalizations.bezout_identity

open Autogeneralize
open Real
open Lean Elab Tactic Meta Term Command

set_option pp.showLetValues false
set_option autoImplicit false
set_option linter.unusedVariables false
-- set_option trace.ProofPrinting true
-- set_option trace.Autogeneralize.abstractPattern true
-- set_option trace.AntiUnify true

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Generalization of the proof that √17 is irrational
to the proof that the square root of any prime is irrational.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Start with the theorem that √17 is irrational. -/
#check irrat_sqrt

example : ∀ (p : ℕ), Nat.Prime p → Irrational √p :=
by

  /- Find the proof-based generalization of 17 to any prime, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sqrt

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of robust generalization of _repeated_ uses of a constant.
Each occurrence of _17_ below generalizes separately.

Generalization of the proof that √17+17 is irrational
to the proof that √p+n is irrational for any prime p and nat n.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Start with the theorem that √17 + 17 is irrational. -/
#check irrat_sum_sqrt

example: ∀ (p n : ℕ), Nat.Prime p → Irrational (√p + n) :=
by
  intros p n p_prime

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sum_sqrt

  exact irrat_sum_sqrt.Gen p p_prime n

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of robust generalization of _repeated_ uses of a constant.
Each occurrence of _3_ below generalizes separately.

Generalization of the proof that that are 3^3 functions from a set A of size 3 to a set B of size 3
to the proof that there are m^n functions from a set A of size n to a set B of size m.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Start with the theorem that there are 3^3 mappings from a set of size 3 to a set of size 3. -/
#check fun_set

example :
  ∀ (n m : ℕ) {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq α],
  Fintype.card α = n → Fintype.card β = m → Fintype.card (α → β) = m ^ n :=
by

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (3 : ℕ) in fun_set

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of robust generalization of _dependent_ uses of a constant.
Generalizing the _2_ below automatically generalizes the _4_.

Generalization of the proof that |A ∪ B| ≤ 4 when |A|=2 and |B|=2
to the proof that |A ∪ B| ≤ n+m when |A|=n and |B|=m
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Start with the theorem that |A ∪ B| ≤ 4 when |A|=2 and |B|=2. -/
#check union_of_finsets

example :
  ∀ (n m : ℕ) {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α),
  A.card = n → B.card = m → (A ∪ B).card ≤ n+m :=
by

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (2:ℕ) in union_of_finsets

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Another demonstration of robust generalization of _dependent_ uses of a constant.
Generalizing the _4_ below automatically generalizes the _3_.

Generalization of the proof that no 4-vertex graph has degree sequence (1,3,3,3)
to the proof that no n-vertex graph has degree sequence (1, n-1, n-1, ..., n-1) when n > 2
(Note that when n=2, a graph with degree sequence (1,1) exists)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/- Start with the theorem that no 4-vertex graph has degree sequence (1,3,3,3) -/
#check impossible_graph

example :
  ∀ (n : ℕ), 2 < n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  ¬(∃ v, G.degree v = 1 ∧ ∀ (w : Fin n), w ≠ v → G.degree w = n - 1) :=
by
  intro n hn

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize (4:ℕ) in impossible_graph

  apply impossible_graph.Gen n (Nat.lt_sub_of_add_lt hn)

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of robust generalization involving abstracting _composite hypotheses_.
When `3` is generalized in the proof below, the algorithm generates a hypothesis `1 < m`
even though the fact `1 < 3` does not occur in directly the proof in the form of a lemma
(but rather, a composite term involving the lemma one_lt_succ_succ applied to the argument 1).

Generalization of the proof that `1 < 3 ^ n` for `n ≠ 0`
to a proof that `1 < m ^ n` for `n ≠ 0` and `m > 1`.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
example : ∀ m, 1 < m → ∀ n, n ≠ 0 → 1 < m ^ n :=
by

  /- Start with the proof that `1 < 3 ^ n` for `n ≠ 0`. -/
  let one_lt_three_pow {n : ℕ} (hn : n ≠ 0) : 1 < 3 ^ n := by
    have hpow_lt : 1 ^ n < 3 ^ n := Nat.pow_lt_pow_left (a := 1) (b := 3) ?_ hn
    rwa [one_pow] at hpow_lt
    · exact Nat.one_lt_succ_succ 1 -- 1 < 3

  /- Find the proof-based generalization. -/
  autogeneralize (3 : ℕ) as m in one_lt_three_pow

  assumption


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of the _occurrences_ flag in the generalization tactic.
Only the first occurence of _17_ below is generalized.

Generalization of the proof that √17+17 is irrational
to the proof that √p+17 is irrational for any prime p.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example: ∀ (p : ℕ), Nat.Prime p → Irrational (√p + 17) :=
by

  /- Only generalize the 17 under the square root. -/
  autogeneralize (17:ℕ) in irrat_sum_sqrt at occurrences [1]

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of _generalizing non-numerical constants_ .

Generalization of the addition operation _+_ in a proof adapted from mathlib's `Int.add_left_cancel`
to a general binary function with certain properties.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Start with the theorem that "a + b = a + c" implies "b = c"
Here, the only hypothesis specific to the integers is `Int.add_left_neg` -/
#check cancellation

example : ∀ (T : Type)        -- If you have an arbitrary type
  [inverse : Neg T]           -- with a symbol representing the inverse,
  (e : T)                     -- and a symbol representing the identity,
  (f : T → T → T),            -- and a binary operation
  (∀ (a : T), f e a = a) →    -- s.t. the identity element is left-neutral w.r.t. the operation
  (∀ (a : T), f (-a) a = e) → -- and every element has a left inverse under the operation
  (∀ (a b c : T), f (f a b) c = f a (f b c)) → -- and the operation is associative,
  ∀ (a b c : T), f a b = f a c → b = c -- then the operation is left-cancellative.
:= by

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize_basic (· + · : ℤ → ℤ → ℤ) in cancellation
  autogeneralize (0) as e in cancellation.Gen
  autogeneralize ℤ in cancellation.Gen.Gen

  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A demonstration of _generalizing non-numerical constants_ .

Generalization of Bezout's identity on the integers _ℤ_
to an arbitrary Euclidean domain.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

 /- Start with Bezout's identity in the integers -/
#check bezout_identity

example := by

  /- Find the proof-based generalization, and add it as a theorem in the context. -/
  autogeneralize ℤ in bezout_identity

  assumption
