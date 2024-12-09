import SatSolver.Dpll

namespace SAT

-- defining the Prop for a formula being satisfiable
def Formula.satisfiable (f : Formula) (a : Assignment) : Prop :=
∀ clause ∈ f, ∃ lit ∈ clause, Literal.eval a lit = some true

/- logical translation between List.all and a Prop explicitly
written using a universal quantification -/
lemma List.forall_of_all {α : Type} (l : List α) (p : α → Bool) :
  (List.all l p) = true → (∀ x ∈ l, p x) = true :=
by
  induction l with
  | nil => simp [List.all]
  | cons hd tl ih =>
    simp [List.all]

/- logical translation between List.any and a Prop explicitly
written using an existential quantification -/
lemma List.exists_of_any {α : Type} (l : List α) (p : α → Bool) :
  (List.any l p) = true → (∃ x ∈ l, p x) = true :=
by
  induction l with
  | nil => simp [List.any]
  | cons hd tl ih =>
    simp [List.any]

/- a universal quantification over an empty domain is true (vacuously)
(this lemma shows this specifically for universal quantifications over
empty lists) -/
lemma forall_nil {α : Type} (P : α → Prop) : ∀ x ∈ ([] : List α), P x :=
  by
    intro x hx
    contradiction

theorem DPLL_sound_assignments (f : Formula) (fuel : ℕ) (a_init : Assignment) :
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
                apply ih f a_false a hDPLL_some h_clause_mem } } } }
    }
  }

/- if calling DPLL on a formula returns some assignment, then the formula
must be satisfiable under that assignment -/
theorem DPLL_sound (f : Formula) (fuel : ℕ) :
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
    apply DPLL_sound_assignments (hd :: tl) (Formula.vars (hd :: tl)).length (fun x => none) a hDPLL_some }

end SAT
