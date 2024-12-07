import SatSolver.SatTypes

namespace SAT

/- checks if a clause is a unit clause under a given assignment
if it is, it returns the unit literal in the clause; else it
returns none -/
def Clause.findUnit (a : Assignment) : Clause → Option Literal :=
  fun clause =>
    if clause.any (λ lit => Literal.eval a lit = some true) then none -- clause already satisfied
    else
      match clause.filter (λ lit => Literal.eval a lit = none) with
      | [lit] => some lit
      | _ => none

/- returns the literal from the first unit clause it finds if it
finds a unit clause; returns none if none of the clauses are unit
clauses -/
def Formula.findUnit (a : Assignment) : Formula → Option Literal :=
  fun f => match f.find? (λ clause => clause.findUnit a ≠ none) with
    | some clause => clause.findUnit a
    | none => none

/- performs unit propagation for a single variable and returns the
updated assignment. If there is no unit clause, no unit propagation
can be performed so none is returned -/
def Formula.unitPropagate (a : Assignment) : Formula → Option Assignment :=
  fun f =>
    match f.findUnit a with
    | none => none
    | some lit =>
      match lit with
      | Literal.pos v => some (λ var => if var = v then some true else a var)
      | Literal.neg v => some (λ var => if var = v then some false else a var)

end SAT
