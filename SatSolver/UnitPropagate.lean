import SatSolver.SatTypes

namespace SAT

/- returns the (only) unassigned literal in the given clause
if the clause is a unit clause; returns none if the clause
is already satisfied, or if it isn't a unit clause -/
def Clause.findUnit (a : Assignment) : Clause → Option Literal :=
  fun clause =>
    if clause.any (λ lit => Literal.eval a lit = some true) then none -- clause already satisfied
    else
      match clause.filter (λ lit => Literal.eval a lit = none) with
      | [lit] => some lit
      | _ => none

/- returns the only unassigned literal from a unit clause in the
formula if there is a unit clause; returns none if the formula has
no unit clasues under the given assignment -/
def Formula.findUnit (a : Assignment) : Formula → Option Literal :=
  fun f => match f.find? (λ clause => clause.findUnit a ≠ none) with
    | some clause => clause.findUnit a
    | none => none

/- performs unit propagation for a single variable and returns the
updated assignment; if there are no unit clauses, the assignment remains
unchanged, so none is returned -/
def Formula.unitPropagate (a : Assignment) : Formula → Option Assignment :=
  fun f =>
    match f.findUnit a with
    | none => none
    | some lit =>
      match lit with
      | Literal.pos v => some (λ var => if var = v then some true else a var)
      | Literal.neg v => some (λ var => if var = v then some false else a var)

end SAT
