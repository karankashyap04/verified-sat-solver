# verified-sat-solver

[Github Repository](https://github.com/karankashyap04/verified-sat-solver)

SAT solvers are increasingly being used to power "automated reasoning" systems. Given the
critical nature of some some applications of these tools, it seems important to verify
the correctness of the SAT solvers we use.

This is an implementation of a DPLL SAT solver in Lean. Additionally, there are some theorems
that verify that some desirable properties hold of the implemented solver.


## DPLL and SAT Solving Overview 

The DPLL (Davis-Putnam-logemann-Loveland) algorithm is used to determine the satisfiability
of propositional formulas that are in Conjunctive Normal Form (CNF) i.e. they are structured
as a disjunction of conjunctions.

A simple example of a **formula** in CNF is `(x1 ∨ x2 ∨ ¬x3) ∧ (¬x1 ∨ ¬x2 ∨ x3)`. This formula is made up
of 2 **clauses**: `(x1 ∨ x2 ∨ ¬x3)` and `(¬x1 ∨ ¬x2 ∨ x3)`. Each of these is a disjunction, and since
the formula is a conjunction of these clauses, the formula as a whole is in CNF.

- `x1`, `x2`, and `x3` here are **variables**. These are boolean entities that can be assigned a truth value.
- `x1`, `¬x1`, `x2`, `¬x2`, `x3`, and `¬x3` are **literals**. Literals are either a variable or its negation,
and they represent the manner in which a variable is evaluated in a clause.

Therefore, overall, a formula is a conjunction of clauses. Each clause is a disjunction of literals.
The goal of DPLL is to consume a formula and determine whether or not their exists an assignment of
truth values to the variables for which the formula will be satisfied (since the formula is a disjunction of
its clauses, this effectively means that each clause needs to be satisfied). <br>
Often (and as has been implemented in this project), SAT solvers don't _just_ determine whether or not a formula
is satisfiable; if it is satisfiable they also return an **assignment** (truth values assigned to the variables)
under which it is satisfiable.

DPLL is a combination of a traditional backtracking tree search algorithm with some additional logical
inferences that help speed things up when possible. These inference mechanisms are:
- Unit Propagation: if a clause (that is not yet satisfied) has only a single unassigned literal (i.e. it is a
**unit clause**), then in order for the clause to be satisfied, that literal must be true under the assignment.
So the relevant variable is assigned a truth value that makes that literal evaluate to true. <br> As a result:
  - Any other clauses that contain the same literal are automatically satisfied 
  - Any clauses containing the negation of the literal can no longer be satisfied by the negation of the literal
  since it will evaluate to false. As a result, new unit clauses might be created. 
- Pure Literal Elimination: if an unassigned variable only exists in its positive or negative form in the clauses
that have not yet been satisfied, then we can safely assign its truth value to be the one that will make all the
literals corresponding to the variable evaluate to true. As a result, all clauses containing the variable will
be immediately satisfied.

The boolean satisfiability problem is NP-complete; however, the DPLL algorithm, combined with clever heuristics for
picking which variable to branch on in the tree search can make SAT solvers quite fast on most instances.


## Representation in Lean 

Given the aforementioned description of how formulas in CNF are structured, we define the following types
in Lean:

```lean
-- Variables (propositional symbols)
inductive Var : Type
  | mk : Nat → Var

-- Literals (variables along with their truth value i.e. pos/neg)
inductive Literal : Type
  | pos : Var → Literal
  | neg : Var → Literal

-- Clauses (disjunction of literals)
def Clause : Type := List Literal

-- Formulae (conjunction of clauses) -- SAT problem represented in CNF
def Formula : Type := List Clause
```

Additionally, we also have a representation for the assignments returned by the 
DPLL algorithm:
```lean
-- Assignments (mapping from variables to their truth values)
def Assignment : Type := Var → Option Bool
```
This maps `Var`s to `Option Bool`s (instead of `Bool`s) to nicely represent partial assignments
(for example, if the `Var` `x1` is unassigned, or if DPLL returns a satisfying assignment in which
the truth value assigned to `x1` is irrelevant, then `x1` can be mapped to `none` in the `Assignment`).

Given these types, we have an implementation of the DPLL function:
```lean
def DPLL (f : Formula) : Option Assignment
```
Given a `Formula` `f`, it returns an `Option Assignment`. If the returned value is `none`, then the formula
is UNSAT (unsatisfiable); if some assignment is returned, then the formula is SAT (satisfiable), and it is
satisfied under the returned assignment. While there are many other helper functions (for performing
unit propagation, pure literal elimination, etc), this is the main DPLL function that would be called when
solving a SAT problem.


## Verifications

There are 2 main properties that have been verified for this implementation of DPLL:
1. If some assignment is returned when DPLL is called on a formula, then the formula _must_ be satisfied
under the returned assignment (SAT results returned by DPLL are truly SAT under the returned assignment).
```lean
theorem DPLL_good_assignments (f : Formula) :
  ∀ a : Assignment, DPLL f = some a → Formula.satisfiable f a
```

2. If there exists no assignment under which a formula is satisfiable, then DPLL returns `none` when called
on the formula (DPLL always says UNSAT if the result is UNSAT).
```lean
theorem DPLL_good_none (f : Formula) :
  (∀ a : Assignment, ¬Formula.satisfiable f a) → DPLL f = none
```

The propositions being proved in each of these theorems references the proposition `Formula.satisfiable`, which
is as follows:
```lean
-- evaluates a literal under a given assignment
def Literal.eval (a : Assignment) : Literal → Option Bool
  | Literal.pos v => a v
  | Literal.neg v =>
    match a v with
    | some b => some (not b)
    | none => none

-- the Prop for a formula being satisfiable 
def Formula.satisfiable (f : Formula) (a : Assignment) : Prop :=
  ∀ clause ∈ f, ∃ lit ∈ clause, Literal.eval a lit = some true
```


## Potential Future Extensions 

While the theorems proven of this implementation certainly increase confidence in the correctness of this
implementation, there is some future work that could be interesting:
- **Prove additional properties**: if there exists _some_ assignment under which a formula is satisfiable, then
calling DPLL on the formula results in an assignment being returned (no false negatives).
- **Make the DPLL implementation more efficient**: in the past, I've spent time implementing SAT solvers with the explicit
goal of trying to make them as fast as possible. A really interesting part of that work was coming up with clever
heuristics for identifying the next variable to branch on as a part of the tree search. This implementation could
be extended with some of these heuristics to improve performance. 
- **Implement a more complex solver**: as a separate (but related) project, it would be interesting to implement more
verified SAT solving algorithms. In particular, I think having a verified CDCL (conflict-driven clause learning)
implementation would be awesome! 
