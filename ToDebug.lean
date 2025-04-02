import AutomaticProofGeneralization.AutoGeneralizeTactic
import AutomaticProofGeneralization.Formalizations.irrationality_of_sqrts

theorem irrat_sqrt' {k : ℕ} (h : k = 17 ∨ 17 = 0) : True :=
  by
    have h' : k = 17 := by { cases h; assumption; have := Nat.Prime.ne_zero prime_seventeen; contradiction };
    trivial

set_option trace.ProofPrinting true
set_option trace.AntiUnify true
example : ∀ (p : ℕ), Nat.Prime p → Irrational √p := by

  /- Find the proof-based generalization of 17 to any prime, and add it as a theorem in the context. -/
  autogeneralize (17:ℕ) in irrat_sqrt'

  assumption
