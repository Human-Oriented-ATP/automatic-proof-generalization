import Lean
open Lean Elab Tactic Meta Term Command


/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Working with function applications
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Returns the argument to an expression e.g. if f has type "n-1=3 → n=4" then it returns "n-1=3"-/
def extractArgType (f : Expr) : MetaM Expr := do
  let fType ← inferType f
  let fType ← whnf fType
  return fType.bindingDomain!
