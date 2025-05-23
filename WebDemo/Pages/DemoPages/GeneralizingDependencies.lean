import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.impossible_graphs
import VersoBlog

set_option pp.showLetValues false

open Verso Genre Blog

#doc (Page) "Handling Dependent Constants" =>

```leanInit generalizingDependentConstants
```

Sometimes when mathematicians generalize a constant $`c`, they generalize not just occurrences of $`c`, but also occurrences of other constants in the proof that _depend_ on $`c`.

# An Example from Set Theory

For example, consider the following theorem, which bounds the size of the union of two sets.

$$`\textrm{If } |A| = 2\ \textrm{ and } |B|=2 \textrm{, then } |A \cup B| \leq 4.`

```lean generalizingDependentConstants
theorem union_of_finsets
  (α : Type) [Fintype α] [DecidableEq α] (A B : Finset α)
  (hA : A.card = 2) (hB : B.card = 2) : (A ∪ B).card ≤ 4 :=
by
  /- Prove it using the fact that |A ∪ B| + |A ∩ B| = |A| + |B|.  -/
  apply hA ▸ hB ▸ Finset.card_union_add_card_inter A B ▸ Nat.le_add_right _ _
```

If we wish to generalize the constant $`2`, it is not enough just to generalize the instances of $`2` itself, since we must also recognise that the constant $`4` depends on the two $`2`s in an important way. Thus, any algorithm that generalizes the $`2`s in the proof will need to generalize the $`4` as well.

The algorithm we present recognizes from a proof of the theorem that the two $`2`s are "independent" and that the $`4` depends on both of them, yielding the following natural generalization.

$$`\textrm{Let } n,m \in \mathbb{N}.\\
\textrm{ If } |A|=n\  \textrm{ and } |B|=m \textrm{, then } |A \cup B| \leq n+m.`


```lean generalizingDependentConstants
theorem union_of_finsets_generalized :
  ∀ (n m : ℕ)
  (α : Type) [Fintype α] [DecidableEq α] (A B : Finset α),
  A.card = n → B.card = m → (A ∪ B).card ≤ n+m :=
by
 /- Generalize the `2`s in the proof to `n` and `m`,
    which automatically generalizes the 4 to `n+m`. -/
  autogeneralize (2:ℕ) in union_of_finsets

  /- Use the generalization to close the goal. -/
  assumption
```

# An Example from Graph Theory

We can also use this program on more complicated mathematical objects.

Consider the following theorem.

$$`\textrm{There is no } 4\textrm{-vertex graph}\\
\textrm{with degree sequence } (1,3,3,3).`

```lean generalizingDependentConstants
theorem nonexistent_graph (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
  ¬(∃ (v : Fin 4), G.degree v = 1 ∧ ∀ w ≠ v, G.degree w = 3) :=
by
  /- We first show that any vertex with degree 3 is adjacent to all other vertices. -/
  rintro ⟨v, v_deg, w_deg⟩; have hw_card : (Set.toFinset {w : Fin 4 | w ≠ v}).card = 3 := by {rw [Set.toFinset_card]; rw [Set.card_ne_eq]; rewrite [Fintype.card_fin]; rfl}; have neq_imp_adj : {w | w ≠ v} ⊆ {w | G.Adj v w} := by {rw [Set.setOf_subset_setOf]; intro w wneqv; apply max_deg_imp_adj_all; rewrite [Fintype.card_fin]; exact (w_deg w wneqv); exact wneqv.symm};

  /- Therefore, the vertex with degree 1 must be adjacent to at least 3 other vertices.-/
  have v_deg_geq : 3 ≤ G.degree v := by {rw [← SimpleGraph.card_neighborFinset_eq_degree]; rw [← hw_card]; apply Finset.card_le_card; unfold SimpleGraph.neighborFinset; unfold SimpleGraph.neighborSet; rw [@Set.toFinset_subset_toFinset]; exact neq_imp_adj}; rw [v_deg] at v_deg_geq;

  /- But, we know the vertex with degree 1 can be adjacent to at most 1 other vertex. Contradiction.-/
  exact Nat.not_lt.mpr v_deg_geq one_lt_three

```

Our program recognizes that the $`4` is a function of the $`3`, and so if we generalize $`4` to $`n`, we must generalize the $`3` to $`n-1`.  Note that the outputted generalization isolates the condition that $`n > 2`, since the graph in the $`n=2` case has degree sequence $`(1,1)`, which does actually exist.

$$`\textrm{For } n > 2, \textrm{there is no } n\textrm{-vertex graph}\\
\textrm{with degree sequence } (1,n-1, \dots, n-1).`


```lean generalizingDependentConstants
theorem nonexistent_graph_generalized  :
  ∀ (n : ℕ), 2 < n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  ¬(∃ v, G.degree v = 1 ∧ ∀ (w : Fin n), w ≠ v → G.degree w = n - 1) :=
by
  intro n hn

  /- Generalize the `4` in the proof to `n`,
  which automatically generalizes the `3`s to `n-1`. -/
  autogeneralize (4:ℕ) in nonexistent_graph

  /- Use the generalization to close the goal. -/
  apply nonexistent_graph.Gen n (Nat.lt_sub_of_add_lt hn)
```


For details on the technical implementation of this dependence-detection, please see the paper "Automatically Generalizing Proofs and Statements."  At a high level, the program determines when one constant is a function of another by replacing each constant with metavariables, and if a typechecking conflict arises in the proof, the program uses the antiunifier of the conflicting expressions to determine the function that relates the two constants.
