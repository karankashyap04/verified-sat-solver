import SatSolver.LoVeLib

namespace SAT

/- ----- TYPES ----- -/

-- Variables (propositional symbols)
inductive Var : Type
  | mk : Nat → Var
deriving DecidableEq, Repr

-- Literals (variables along with their truth value i.e. pos/neg)
inductive Literal : Type
  | pos : Var → Literal
  | neg : Var → Literal
deriving DecidableEq, Repr

-- Clauses (disjunction of literals)
def Clause : Type := List Literal
deriving DecidableEq, Membership

-- Formulae (conjunction of clauses) -- SAT problem represented in CNF
def Formula : Type := List Clause
deriving DecidableEq, Membership

-- Assignments (mapping from variables to their truth values)
def Assignment : Type := Var → Option Bool
/- [note]: this is a function from variables to optional bools, to allow
for partial assignments as we go along in the DPLL algorithm -/


/- ----- BASIC FUNCTIONS ----- -/

-- returns the variable associated with a given literal
def Literal.var : Literal → Var
  | Literal.pos v => v
  | Literal.neg v => v

-- returns the negation of a given literal
def Literal.negate : Literal → Literal
  | Literal.pos v => Literal.neg v
  | Literal.neg v => Literal.pos v

-- determines if a given literal is positive
def Literal.isPos : Literal → Bool
  | Literal.pos _ => true
  | Literal.neg _ => false

-- determines if a given literal is negated (negative)
def Literal.isNeg : Literal → Bool :=
  fun lit => !lit.isPos

-- returns the number of variables in a given formula
def Formula.vars (f : Formula) : List Var :=
  f.map (λ clause => clause.map (λ lit => lit.var))
  |> List.join
  |> List.dedup

-- evaluates a literal under the given assignment
def Literal.eval (a : Assignment) : Literal → Option Bool
  | Literal.pos v => a v
  | Literal.neg v =>
    match a v with
    | some b => some (not b)
    | none => none

-- determines if a clause is unsatisfiable under the given assignment
def Clause.isUNSAT (a : Assignment) : Clause → Bool :=
  fun clause => clause.all (λ lit => Literal.eval a lit = some false)

-- determines if a clause is satisfied under the given assignment
def Clause.isSAT (a : Assignment) : Clause → Bool :=
  fun clause => clause.any (λ lit => Literal.eval a lit = some true)

-- determines if a formula is unsatisfiable under the given assignment
def Formula.isUNSAT (a : Assignment) : Formula → Bool :=
  fun f => f.any (λ clause => clause.isUNSAT a)

-- determines if a formula is satisfied under the given assignment
def Formula.isSAT (a : Assignment) : Formula → Bool :=
  fun f => f.all (λ clause => clause.isSAT a)

end SAT
