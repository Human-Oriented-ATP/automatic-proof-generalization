import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts
import Mathlib.Data.Fintype.Pi
import VersoBlog

set_option pp.showLetValues false

open Verso Genre Blog

#doc (Page) "Handling Dependent Constants" =>

```leanInit generalizingDependentConstants
```

Sometimes when mathematicians say that they wish to generalize a constant $`c`, they really need to generalize not just occurrences of $`c`, but also occurrences of other constants in the proof that _depend_ on $`c`.

# Dummy Title

For example, consider the following theorem, which bounds the size of the union of two sets.  It says that if $`|A|=2` and $`|B|=2`, then $`|A ∪ B| ≤ 4`.

```lean generalizingDependentConstants
theorem union_of_finsets
  (α : Type) [Fintype α] [DecidableEq α]
  (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2) : (A ∪ B).card ≤ 4 :=
by
  /- Prove it using the fact that |A ∪ B| + |A ∩ B| = |A| + |B|.  -/
  apply hA ▸ hB ▸ Finset.card_union_add_card_inter A B ▸ Nat.le_add_right _ _
```

If we wish to generalize the constant $`2`, it is not enough just to generalize the instances of $`2` itself, since we must also recognise that the constant $`4` depends on the two $`2`s in an important way. Thus, any algorithm that generalizes the $`2`s in the proof will need to generalize the $`4` as well.

The algorithm we present recognizes from a proof of the theorem that the two $`2`s are "independent" and that the $`4` depends on both of them, yielding the following natural generalization.

```lean generalizingDependentConstants
theorem union_of_finsets_generalized :
  ∀ (n m : ℕ)
  (α : Type) [Fintype α] [DecidableEq α] (A B : Finset α),
  A.card = n → B.card = m → (A ∪ B).card ≤ n+m :=
by

 /- Generalize the `2`s in the proof to `n` and `m`,
    which automatically generalizes the 4 to `n+m`. -/
  autogeneralize (2:ℕ) in union_of_finsets

  assumption
```
