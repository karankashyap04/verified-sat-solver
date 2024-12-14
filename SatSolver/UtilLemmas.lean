import SatSolver.LoVeLib

namespace SAT

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

end SAT
