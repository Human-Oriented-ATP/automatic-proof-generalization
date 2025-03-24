import AutomaticProofGeneralization.AutoGeneralizeTactic
import Mathlib.Tactic

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

example : True := by
  -- a proof of `1 < 3` that does not use `3` anywhere in the proof
  let one_lt_three : 1 < 3 := Nat.one_lt_succ_succ 1
  -- the generalized statement produces `1 < 1.succ.succ`
  -- instead of a more general statement
  autogeneralize (3 : ℕ) in one_lt_three
  trivial


theorem dvd_left_of_dvd_prod {a b c : ℤ} (h : a ∣ b) : a ∣ (b * c) := by
  /- This step is using the fact that `a ∣ b` is defined over the integers as `∃ d, d * a = b`
     to extract out a witness `d : ℤ` satisfying `d * a = b` from the hypothesis `h`.
     This step breaks when `ℤ` is replaced by an arbitrary type. -/
  rcases h with ⟨d, hd⟩
  use (d * c)
  rw [hd, mul_assoc]

set_option trace.AntiUnify true

example : True := by
  first
    | autogeneralize ℤ in dvd_left_of_dvd_prod
    | dbg_trace "Generalization threw an error"
  trivial

theorem dvd_left_of_dvd_prod_fixed {a b c : ℤ} (h : a ∣ b) : a ∣ (b * c) := by
  rw [Int.dvd_def] at * -- expand `a ∣ b` to `∃ d, d * a = b` everywhere
  rcases h with ⟨d, hd⟩ -- obtain the `d` such that `a * d = b` from hypothesis `h`, which now has the correct type
  use (d * c)
  rw [hd, mul_assoc]

example : True := by
  first
    | autogeneralize ℤ in dvd_left_of_dvd_prod_fixed
    | dbg_trace "Generalization threw an error"
  trivial
