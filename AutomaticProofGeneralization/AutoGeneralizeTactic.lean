import Lean
import AutomaticProofGeneralization.Helpers.GoalsAndHypotheses
import AutomaticProofGeneralization.Helpers.ReplacePatternWithMVars
import AutomaticProofGeneralization.Helpers.Simplification
import AutomaticProofGeneralization.Helpers.Unification

open Lean Elab Tactic Meta Term Command

namespace Autogeneralize

initialize
  registerTraceClass `ProofPrinting

/-- Generalize a term in a theorem to an arbitrary constant of its type, adding in necessary hypotheses along the way -/
def autogeneralize (thmName : Name) (pattern : Expr) (customName? : Option Name := none) (occs : Occurrences := .all) (consolidate : Bool := false) : TacticM Unit := withMainContext do
  -- Get details about the un-generalized proof we're going to generalize
  let (thmType, thmProof) ← getTheoremAndProof thmName
  trace[ProofPrinting] m!"Initial Proof: { thmProof}"

  -- Get the generalized theorem (replace instances of pattern with mvars)
  let mut genThmProof := thmProof
  let mut dependenciesToGeneralize := [] -- keep track of dependencies of what must be generalized first
  (_, dependenciesToGeneralize) ← replacePatternWithMVars genThmProof pattern (← getLCtx) (← getLocalInstances) |>.run [] -- replace instances of f's old value with metavariables

  -- Generalize all constants that `pattern` has dependencies on, and then generalize `pattern`
  dependenciesToGeneralize := dependenciesToGeneralize.eraseDups ++ [pattern]
  trace[ProofPrinting] m!"We are abstracting the following constants: { dependenciesToGeneralize}"
  for dep in dependenciesToGeneralize do
    genThmProof ← replacePatternWithMVars genThmProof dep (← getLCtx) (← getLocalInstances) |>.run' []

  trace[ProofPrinting] m!"Generalized Proof After Abstraction: {genThmProof}"

  -- Consolidate mvars within proof term by running a typecheck
  genThmProof ← consolidateWithTypecheck genThmProof
  trace[ProofPrinting] m!"Generalized Proof After Typecheck: {genThmProof}"
  let genThmType ← inferType genThmProof

  -- Re-specialize the occurrences of the pattern we are not interested in
  if !(occs == .all) then do
    genThmProof ← respecializeOccurrences thmType genThmProof pattern (occsToStayAbstracted := occs) consolidate

  -- (If desired) make all abstracted instances of the pattern the same.
  if consolidate then do
    let mvarsInProof := (← getMVars genThmProof) ++ (← getMVars genThmType)
    setEqualAllMVarsOfType mvarsInProof (← inferType pattern)

  -- Remove repeating hypotheses
  genThmProof ← removeRepeatingHypotheses genThmProof

  -- Give the meta-variables in the proof more human-readable names
  relabelMVarsIn genThmProof customName?
  trace[ProofPrinting] m!"Generalized Proof After Renaming: {genThmProof}"

  -- Pull out the holes (the abstracted term & all hypotheses on it) into a chained implication.
  genThmProof ←  pullOutMissingHolesAsHypotheses genThmProof
  let genThmType ← inferType genThmProof

  -- Add the generalized theorem to the context.
  createLetHypothesis genThmType genThmProof (thmName++`Gen)

  logInfo m!"Successfully generalized \n  {thmName} \nto \n  {thmName++`Gen} : {genThmType} \nby abstracting {← ppExpr pattern}."

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Autogeneralizes the "pattern" in the hypothesis "h",
But generalizes all occurrences in the same way.  Behaves as in (Pons, 2000)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

syntax customName := "as" ident
def decodeCustomName (stx? : Option (TSyntax ``customName)) : Option Name :=
  stx?.bind fun
    | `(customName| as $name) => some name.getId
    | _ => none

/-- A tactic that generalizes all instances of `pattern` in a local hypotheses `h` by requiring `pattern` to have only the properties used in the proof of `h`.
    Behaves as in ("Generalization in Type Theory Based Proof Assistants" by Olivier Pons, 2000) in that it doesn't generalize repeated constants in different ways
    But with the additional capability of generalizing dependent constants -/
elab "autogeneralize_basic" pattern:term customName?:(customName)? "in" h:ident : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  let customName? := decodeCustomName customName?
  autogeneralize h pattern customName? (occs:=.all) (consolidate:=true)

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Autogeneralizes the "pattern" in the hypothesis "h",
Default behavior is to generalizes all occurrences separately, but can generalize at specified occurences.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/
/- Parse occurrences of the term as specified by the user.-/
syntax occurrences :="at" "occurrences" "[" num+ "]"
def decodeOccurrences : TSyntax `Autogeneralize.occurrences → List Nat
  | `(occurrences| at occurrences [$occs*]) => (occs.map TSyntax.getNat).toList
  | _ => unreachable!


/-- A tactic that generalizes all instances of `pattern` in a local hypotheses `h` by requiring `pattern` to have only the properties used in the proof of `h`.-/
elab "autogeneralize" pattern:term customName?:(customName)? "in" h:ident occs:(Autogeneralize.occurrences)? : tactic => do
  let pattern ← (Lean.Elab.Term.elabTerm pattern none)
  let h := h.getId
  let occs := occs.map decodeOccurrences
  let customName? := decodeCustomName customName?
  match occs with
  | some occsList => autogeneralize h pattern customName? (Occurrences.pos occsList)
  | none => autogeneralize h pattern customName? -- generalize all occurrences (default: to different mvars)

end Autogeneralize
