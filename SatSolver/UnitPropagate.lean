import SatSolver.SatTypes
import SatSolver.LoVeLib

namespace SAT

/- checks if a clause is a unit clause under a given assignment
if it is, it returns the unit literal in the clause; else it
returns none -/
def Clause.isUnit : Clause → Option Literal
  | [lit] => some lit
  | _ => none

/- simplifies clauses by removing literals that are false under
the given assignment (since those literals couldn't possibly satisfy
the clause under this assignment) -/
def Clause.simplify (a : Assignment) : Clause → Clause
  | [] => []
  | lit :: lits =>
    match Literal.eval a lit with
    | some false => Clause.simplify a lits -- exclude lit
    | _ => lit :: Clause.simplify a lits

/- simplifies the formula by
    1. removing all clauses that are already satisfied
    2. simplifying all clauses -/
def Formula.simplify (a : Assignment) : Formula → Formula
  | [] => []
  | clause :: clauses =>
    let clause' := Clause.simplify a clause
    match clause'.find? (λ lit => Literal.eval a lit = some true) with
    | some _ => Formula.simplify a clauses -- exclude clause since it is satisfied
    | none => clause' :: Formula.simplify a clauses

/- returns the literal from the first unit clause it finds if it
finds a unit clause; returns none if none of the clauses are unit
clauses -/
def Formula.findUnit : Formula → Option Literal
  | [] => none
  | clause :: clauses =>
    match clause.isUnit with
    | some lit => some lit
    | none => Formula.findUnit clauses

/- helper function for performing unit propagation on a formula -- this
includes an extra variable `fuel` in the recursion -- it serves no
functional purpose beyond being a term that clearly decreases in the
recursive calls, allowing Lean to identify that this function actually
terminates -/
def Formula.unitPropagateAux (a : Assignment) : Formula → Nat → Assignment × Formula
  | [], _ => (a, []) -- formula is empty (already SAT)
  | f, 0 => (a, f) -- safeguard: prevent infinite recursion
  | f, Nat.succ fuel =>
    match f.findUnit with
    | none => (a, f) -- no unit clause found
    | some lit => -- unit clause found (need to propagate lit)
      match lit with
      | Literal.pos v =>
        let a' := λ var => if var = v then some true else a var
        let f' := f.simplify a'
        Formula.unitPropagateAux a' f' fuel
      | Literal.neg v =>
        let a' := λ var => if var = v then some false else a var
        let f' := f.simplify a'
        Formula.unitPropagateAux a' f' fuel

/- perform unit propagation on a formula -/
def Formula.unitPropagate (a : Assignment) (f : Formula) : Assignment × Formula :=
  Formula.unitPropagateAux a f f.length

end SAT
