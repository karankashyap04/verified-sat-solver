import SatSolver.SatTypes

namespace SAT

def Formula.findPureLiteral (a : Assignment) : Formula → Option Literal :=
  fun f =>
    let clausesNotYetSatisfied := f.filter (λ clause => ¬clause.isSAT a)
    let lits := clausesNotYetSatisfied.join.dedup.filter (λ lit => a lit.var = none)
    let posLits := lits.filter (λ lit => lit.isPos)
    let negLits := lits.filter (λ lit => lit.isNeg)
    let pureLits := posLits.diff (negLits.map Literal.negate) ++ negLits.diff (posLits.map Literal.negate)
    match pureLits with
    | [lit] => some lit
    | _ => none

def Formula.pureLiteralEliminate (a : Assignment) : Formula → Option Assignment :=
  fun f =>
    match f.findPureLiteral a with
    | none => none
    | some lit =>
      match lit with
      | Literal.pos v => some (λ var => if var = v then some true else a var)
      | Literal.neg v => some (λ var => if var = v then some false else a var)

end SAT
