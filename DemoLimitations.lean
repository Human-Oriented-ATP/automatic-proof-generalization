/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Demos where the current implementation produces suboptimal outputs.
Highlights possibilities for future work.
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/

import AutomaticProofGeneralization.AutoGeneralizeTactic
import Mathlib.Tactic

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING WITH DEFINITIONAL EQUALITY.
Demonstration that
- - - - - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - -/

theorem dvd_left_of_dvd_prod {a b c : ℤ} (h : a ∣ b) : a ∣ (b * c) := by
  /- This step is using the fact that `a ∣ b` is defined over the integers as `∃ d, d * a = b`
     to extract out a witness `d : ℤ` satisfying `d * a = b` from the hypothesis `h`.
     This step breaks when `ℤ` is replaced by an arbitrary type. -/
  rcases h with ⟨d, hd⟩
  exists (d * c)
  rw [hd, mul_assoc]

set_option trace.AntiUnify true

example : True := by -- this generalization fails
  first -- the `first` tactic combinator runs the first tactic in the sequence that succeeds
    | autogeneralize ℤ in dvd_left_of_dvd_prod
    | dbg_trace "Generalization threw an error"
  trivial

theorem dvd_left_of_dvd_prod_fixed {a b c : ℤ} (h : a ∣ b) : a ∣ (b * c) := by
  rw [Int.dvd_def] at * -- expand `a ∣ b` to `∃ d, d * a = b` everywhere
  rcases h with ⟨d, hd⟩ -- obtain the `d` such that `a * d = b` from hypothesis `h`, which now has the correct type
  exists (d * c)
  rw [hd, mul_assoc]

example : True := by -- this generalization succeeds
  autogeneralize ℤ in dvd_left_of_dvd_prod_fixed
  trivial

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING WITH COMPUTATION RULES.
Demonstration that compatible proofs must use deduction rules, not computation rules
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- An example where only deduction rules are used, so the proof generalizes. -/
example : ∀ (n : ℕ), Even (2 * n) := by
  let two_times_three_is_even : Even (2*3) := by {unfold Even; apply Exists.intro 3; rw [two_mul]}
  autogeneralize 3 in two_times_three_is_even
  assumption


/- An example where "3" doesn't show up in the proof term (due to use of the computation rule reduceMul), so the proof doesn't generalize. -/
example := by
  let two_times_three_is_even : Even (2*3) := by simp only [Nat.reduceMul]; rw [@Nat.even_iff]
  first -- the `first` tactic combinator runs the first tactic in the sequence that succeeds
    | autogeneralize 3 in two_times_three_is_even -- throws error b/c of computation rule
    | dbg_trace "Generalization threw an error."
  assumption

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
GENERALIZING HAVE STATEMENTS
Demonstration that the tactic can only generalize proofs of `let statements, since Lean doesn't allow us access to the proofs of 'have' statements.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

example := by
  have one_plus_one : 1+1=2 := by simp only [Nat.reduceAdd]
  first -- the `first` tactic combinator runs the first tactic in the sequence that succeeds
    | autogeneralize 3 in one_plus_one -- throws error b/c of computation rule
    | dbg_trace "Generalization threw an error, since it can't access the proof of a 'have' statement."
  assumption
