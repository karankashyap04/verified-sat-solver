import SatSolver.Dpll
import SatSolver.UtilLemmas

namespace SAT

-- defining the Prop for a formula being satisfiable
def Formula.satisfiable (f : Formula) (a : Assignment) : Prop :=
∀ clause ∈ f, ∃ lit ∈ clause, Literal.eval a lit = some true

/- helper lemma for DPLL_good_assignments (below) -/
lemma DPLL_aux_good_assignments (f : Formula) (fuel : ℕ) (a_init : Assignment) :
  ∀ a : Assignment, DPLL_aux a_init f fuel = some a → Formula.satisfiable f a :=
by
  intro a hDPLL_some
  simp only [Formula.satisfiable]
  intro clause h_clause_mem
  induction fuel generalizing f a_init a with
  | zero => {
    unfold DPLL_aux at hDPLL_some
    simp at hDPLL_some }
  | succ n ih => {
    unfold DPLL_aux at hDPLL_some
    cases hSAT : f.isSAT a_init with
    | true => {
      rw [hSAT] at hDPLL_some
      simp at hDPLL_some
      unfold Formula.isSAT at hSAT
      have h : (∀ c ∈ f, c.isSAT a_init) = true := by {
        apply List.forall_of_all _ _ hSAT
      }
      simp at h
      have h1 := h clause h_clause_mem
      have h2 : (∃ lit ∈ clause, decide (Literal.eval a_init lit = some true)) = true := by {
        apply List.exists_of_any _ _ h1
      }
      simp at h2
      rw [hDPLL_some] at h2
      exact h2 }
    | false => {
      have h_notSAT : Formula.isSAT a_init f = false := by aesop
      rw [h_notSAT] at hDPLL_some
      simp at hDPLL_some
      cases hUNSAT : f.isUNSAT a_init with
      | true => {
        rw [hUNSAT] at hDPLL_some
        simp at hDPLL_some }
      | false => {
        have h_notUNSAT : Formula.isUNSAT a_init f = false := by aesop
        rw [h_notUNSAT] at hDPLL_some
        simp at hDPLL_some
        cases h_pure : f.pureLiteralEliminate a_init with
        | some a' => {
          rw [h_pure] at hDPLL_some
          simp at hDPLL_some
          apply ih f a' a hDPLL_some h_clause_mem }
        | none => {
          rw [h_pure] at hDPLL_some
          simp at hDPLL_some
          cases h_up : f.unitPropagate a_init with
          | some a' => { -- some unit propagation occurred
            rw [h_up] at hDPLL_some
            simp at hDPLL_some
            apply ih f a' a hDPLL_some h_clause_mem }
          | none => { -- no unit propagation occurred (so we will branch on a variable)
            rw [h_up] at hDPLL_some
            simp at hDPLL_some
            cases hchoose : f.chooseVar2 a_init with
            | none => { -- no variable to branch on (shouldn't happen)
              rw [hchoose] at hDPLL_some
              simp at hDPLL_some }
            | some lit => {
              rw [hchoose] at hDPLL_some
              simp at hDPLL_some
              generalize h_atrue : (λ var => if var = lit.var then some true else a_init var) = a_true
              rw [h_atrue] at hDPLL_some
              cases hbranch : DPLL_aux a_true f n with
                | some a' => {
                  rw [hbranch] at hDPLL_some
                  simp at hDPLL_some
                  rw [← hDPLL_some]
                  apply ih f a_true a' hbranch h_clause_mem }
                | none => {
                  generalize h_afalse : (λ var => if var = lit.var then some false else a_init var) = a_false
                  rw [h_afalse] at hDPLL_some
                  rw [hbranch] at hDPLL_some
                  simp at hDPLL_some
                  apply ih f a_false a hDPLL_some h_clause_mem } } }
         } }
    }
  }

/- helper lemma for DPLL_good_none (below) -/
theorem DPLL_aux_good_none (f : Formula) (fuel : ℕ) (a_init : Assignment) :
  (∀ a : Assignment, ¬f.satisfiable a) → DPLL_aux a_init f fuel = none :=
by
  intro hUNSAT
  induction fuel generalizing f a_init with
  | zero => {
    unfold DPLL_aux
    simp
   }
  | succ n ih => {
    unfold DPLL_aux
    cases hf : f with
    | nil => {
      unfold DPLL_aux
      simp [hf] at hUNSAT
      unfold Formula.satisfiable at hUNSAT
      simp at hUNSAT
      have h := hUNSAT a_init
      obtain ⟨_, hClauseInF, _⟩ := h
      contradiction
    }
    | cons clause rest => {
      simp
      cases hfSAT : Formula.isSAT a_init (clause :: rest) with
      | true => {
        simp
        have h := hUNSAT a_init
        unfold Formula.isSAT at hfSAT
        have hSAT := List.forall_of_all (clause :: rest) (fun c => c.isSAT a_init) hfSAT
        rw [← hf] at hSAT
        simp at hSAT
        unfold Clause.isSAT at hSAT
        unfold Formula.satisfiable at h
        simp at h
        obtain ⟨c, hmem, hcUNSAT⟩ := h
        have hcSAT := hSAT c hmem
        have hcSAT' := List.exists_of_any c (fun lit => decide (Literal.eval a_init lit = some true)) hcSAT
        simp at hcSAT'
        obtain ⟨lit, hLitInC, hLitEval⟩ := hcSAT'
        apply hcUNSAT lit hLitInC hLitEval
      }
      | false => {
        simp
        cases hfUNSAT : Formula.isUNSAT a_init (clause :: rest) with
        | true => { simp }
        | false => {
          simp
          rw[← hf]
          cases hpure : Formula.pureLiteralEliminate a_init f with
          | some a' => {
            simp
            apply ih f a' hUNSAT
           }
          | none => {
            simp
            cases hup : Formula.unitPropagate a_init f with
            | some a' => {
              simp
              apply ih f a' hUNSAT
            }
            | none => {
              simp
              cases hchoose : Formula.chooseVar2 a_init f with
              | none => { simp }
              | some lit => {
                simp
                generalize h_atrue : (λ var => if var = lit.var then some true else a_init var) = a_true
                cases hbranch : DPLL_aux a_true f n with
                | some a' => {
                  simp
                  have h := DPLL_aux_good_assignments f n a_true a' hbranch
                  have h' := hUNSAT a'
                  contradiction
                }
                | none => {
                  simp
                  generalize h_afalse : (λ var => if var = lit.var then some false else a_init var) = a_false
                  cases hbranch' : DPLL_aux a_false f n with
                  | some a' => {
                    simp
                    have h := DPLL_aux_good_assignments f n a_false a' hbranch'
                    have h' := hUNSAT a'
                    contradiction
                  }
                  | none => { simp } } } } } } } } }

/- if calling DPLL on a formula returns some assignment, then the formula
must be satisfiable under that assignment -/
theorem DPLL_good_assignments (f : Formula) :
  ∀ a : Assignment, DPLL f = some a → Formula.satisfiable f a :=
by
  intro a hDPLL_some
  unfold DPLL at hDPLL_some
  cases hf : f with
  | nil => {
    unfold Formula.satisfiable
    apply forall_nil }
  | cons hd tl => {
    rw [hf] at hDPLL_some
    simp at hDPLL_some
    apply DPLL_aux_good_assignments (hd :: tl) ((Formula.vars (hd :: tl)).length + 1) (fun x => none) a hDPLL_some }

/- if a formula is not satisfiable for any possible assignment, then calling
DPLL on that formula returns none (represents UNSAT) -/
theorem DPLL_good_none (f : Formula) :
  (∀ a : Assignment, ¬Formula.satisfiable f a) → DPLL f = none :=
by
  intro hUNSAT
  unfold DPLL
  cases hf : f with
  | nil => {
    simp
    simp [hf] at hUNSAT
    unfold Formula.satisfiable at hUNSAT
    have h := hUNSAT (fun x => none)
    simp at h
    obtain ⟨_, hClauseInF, _⟩ := h
    contradiction
    }
  | cons hd tl => {
    simp
    rw [← hf]
    apply DPLL_aux_good_none f ((Formula.vars f).length + 1) (fun x => none) hUNSAT }

end SAT
