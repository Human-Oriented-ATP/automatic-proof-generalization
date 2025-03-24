import Lean
open Lean Elab Tactic Meta Term Command

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with names
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

def placeholderName := `placeholder
def preferredNames := #[`n, `m, `p, `a, `b, `c] -- preferred names for numbers
def typePreferredNames := #[`T, `R, `P] -- preferred names for types
def funcPreferredNames := #[`f, `g, `h] -- preferred names for functions

/-- Relabel the metavariables in the expression with their preferred names. -/
def relabelMVarsIn (e : Expr) : MetaM Unit := do
  let mvars ← getMVars e
  let placeholderMVars ← mvars.filterM fun mvar => do
    return (← mvar.getTag).getRoot.toString.startsWith placeholderName.toString

  -- Group mvars by their type
  let mut typeMVars := #[]
  let mut funcMVars := #[]
  let mut otherMVars := #[]

  for mvar in placeholderMVars do
    let mvarType ← mvar.getType
    if mvarType.isType then
      typeMVars := typeMVars.push mvar
    else if mvarType.isArrow then
      funcMVars := funcMVars.push mvar
    else
      otherMVars := otherMVars.push mvar

  -- Assign names based on type
  for (mvar, name) in typeMVars.zip typePreferredNames do
    mvar.setUserName name
  for (mvar, name) in funcMVars.zip funcPreferredNames do
    mvar.setUserName name
  for (mvar, name) in otherMVars.zip preferredNames do
    mvar.setUserName name

/-- Turn a lemma name into its generalized version by prefixing it with `gen_` and truncating. -/
def mkAbstractedName (n : Name) : Name :=
    match n with
    | (.str _ s) =>  Name.mkSimple s!"gen_{s.takeWhile (fun c => c != '_')}"
    | _ => `unknown
