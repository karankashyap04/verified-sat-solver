import SatSolver.SatTypes
import SatSolver.UnitPropagate
import SatSolver.ReprInstances

namespace SAT

/- checks if a given formula is already UNSAT (if it contains
an empty clause) -/
def Formula.isUNSAT : Formula → Bool
  | [] => false
  | clause :: clauses =>
    match clause with
    | [] => true
    | _ => Formula.isUNSAT clauses

/- chooses an unassigned variable as the next branching variable
in the tree search -/
def Formula.chooseVar (f : Formula) (a : Assignment) : Option Var :=
  let c := f.find? (λ clause => clause.any (λ lit => a lit.var = none))
  -- c is a clause that contains an unassigned variable
  match c with
  | none => none
  | some clause => -- get the literal from the clause, and return its variable
    (clause.find? (λ lit => a lit.var = none)).bind (λ lit => some lit.var)

/- DPLL algorithm (for solving boolean satisfiability problem)
returns an Assignment if a satisfying assignment exists; else
returns none -/
def DPLL_aux (a : Assignment) : Formula → ℕ → Option Assignment
  | [], _ => some a -- empty formula so already SAT
  | f, 0 => none -- safeguard to prevent infinite recursion
  | f, Nat.succ fuel =>
    if f.isUNSAT then none else
    let (a', f') := f.unitPropagate a
    match f' with
    | [] => some a' -- formula is now SAT
    | _ =>
      if f'.isUNSAT then none else
      match f'.chooseVar a' with
      | none => none -- we should never get here
      | some v =>
        let a_true := λ var => if var = v then some true else a' var
        let tryTrue := DPLL_aux a_true (f'.simplify a_true) fuel
        match tryTrue with
        | some a'' => some a''
        | none =>
          let a_false := λ var => if var = v then some false else a' var
          DPLL_aux a_false (f'.simplify a_false) fuel

def DPLL (a : Assignment) (f : Formula) : Option Assignment :=
  DPLL_aux a f (f.vars.length)

-- def displayResult (result : Option Assignment) (f : Formula) : String :=
--   match result with
--   | none => "UNSAT"
--   | some a => "SAT: " ++
--     String.intercalate ", " (f.vars.map (λ var => s!"{repr var} := {repr (a var)}"))


-- -- EXAMPLE
-- def exampleFormula : Formula :=
--   [[Literal.pos (Var.mk 0), Literal.neg (Var.mk 1)], [Literal.neg (Var.mk 0), Literal.pos (Var.mk 1)]]

-- def satResult : Option Assignment :=
--   DPLL (λ _ => none) exampleFormula
-- #eval displayResult satResult exampleFormula

end SAT
