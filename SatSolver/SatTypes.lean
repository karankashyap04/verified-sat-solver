namespace SAT

-- Variables (propositional symbols)
inductive Var : Type
  | mk : Nat → Var

-- Literals (variables along with their truth value i.e. pos/neg)
inductive Literal : Type
  | pos : Var → Literal
  | neg : Var → Literal

-- negation of a literal
def Literal.negate : Literal → Literal
  | Literal.pos v => Literal.neg v
  | Literal.neg v => Literal.pos v

-- Clauses (disjunction of literals)
def Clause : Type := List Literal

-- Formulae (conjunction of clauses) -- SAT problem represented in CNF
def Formula : Type := List Clause

-- Assignments (mapping from variables to their truth values)
def Assignment : Type := Var → Option Bool
/- [note]: this is a function from variables to optional bools, to allow
for partial assignments as we go along in the DPLL algorithm -/

-- evaluates a literal under some given assignment
def Literal.eval (a : Assignment) : Literal → Option Bool
  | Literal.pos v => a v
  | Literal.neg v =>
    match a v with
    | some b => some (not b)
    | none => none

end SAT
