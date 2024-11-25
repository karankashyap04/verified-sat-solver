import SatSolver.SatTypes

namespace SAT

/-- `Repr` instance for `Var` -/
instance : Repr Var where
  reprPrec
    | Var.mk n, _ => s!"Var {n}"

/-- `Repr` instance for `Literal` -/
instance : Repr Literal where
  reprPrec
    | Literal.pos v, _ => s!"Pos {repr v}"
    | Literal.neg v, _ => s!"Neg {repr v}"

/-- `Repr` instance for `Option Bool` -/
instance : Repr (Option Bool) where
  reprPrec
    | none, _ => "none"
    | some a, _ => s!"{repr a}"

end SAT
