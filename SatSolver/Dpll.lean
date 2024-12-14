import SatSolver.SatTypes
import SatSolver.UnitPropagate
import SatSolver.PureLiteralEliminate
import SatSolver.ReprInstances

namespace SAT

/- returns the first unassigned variable (under the given
assignment) from the literals in the given clause;
if the variables associated with all the literals in the
given clause are already assigned under the given assignment,
then none is returned -/
def Clause.chooseVar (a : Assignment) : Clause → Option Literal :=
  fun clause => clause.find? (λ lit => a lit.var = none)

/- chooses a variable for branching in the tree search;
returns the first variable associated with a literal in an
unsatisfied clause that is not yet assigned; if no such
variable exists, then none is returned -/
def Formula.chooseVar (a : Assignment) : Formula → Option Literal :=
  fun f =>
    match (f.filter (λ clause => not (clause.isSAT a))).find? (λ clause => clause.chooseVar a ≠ none) with
    | some clause => clause.chooseVar a
    | none => none

/- DPLL helper function using a measure (of type ℕ) to show Lean a strict subterm in
recursive calls so it can guarantee termination -/
def DPLL_aux (a : Assignment) : Formula → ℕ → Option Assignment
  | f, 0 => none -- shows Lean termination (no infinite recursion)
  | f, Nat.succ fuel =>
    if f.isSAT a then some a
    else if f.isUNSAT a then none
    else
      match f.pureLiteralEliminate a with
      | some a' => DPLL_aux a' f fuel
      | none =>
        match f.unitPropagate a with
        | some a' => DPLL_aux a' f fuel
        | none =>
          match f.chooseVar a with
          | none => none -- no unassigned variables (shouldn't happen)
          | some lit =>
            let a_true := λ var => if var = lit.var then some true else a var
            match DPLL_aux a_true f fuel with
            | some a' => some a'
            | none =>
              let a_false := λ var => if var = lit.var then some false else a var
              DPLL_aux a_false f fuel

/- DPLL algorithm - returns an assignment under which the given formula
is satisfied if such an assignment exists; else returns none -/
def DPLL (f : Formula) : Option Assignment :=
  if f = [] then some (λ _ => none) else
    DPLL_aux (λ _ => none) f (f.vars.length + 1)

-- def displayResult (result : Option Assignment) (f : Formula) : String :=
--   match result with
--   | none => "UNSAT"
--   | some a => "SAT: " ++
--     String.intercalate ", " (f.vars.map (λ var => s!"{repr var} := {repr (a var)}"))

-- EXAMPLE
-- def exampleFormula : Formula :=
--   [[Literal.pos (Var.mk 0), Literal.neg (Var.mk 1)], [Literal.neg (Var.mk 0), Literal.pos (Var.mk 1)]]

-- def satResult : Option Assignment :=
--   DPLL exampleFormula
-- #eval displayResult satResult exampleFormula

end SAT
