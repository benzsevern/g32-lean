import HodgeLean.Foundations.QuotientDuality.PersistencePatchComposition

/-! Actual endpoint neighbourhoods for ordered ambient patch composites. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- Points reaching one of the listed endpoint neighbourhoods at its application stage. -/
def persistencePatchNeighbourhood {X ι : Type*} [TopologicalSpace X]
    (O : ι → Set X) (R : ι → C(X, X)) : List ι → Set X
  | [] => ∅
  | i :: l => O i ∪ (R i) ⁻¹' persistencePatchNeighbourhood O R l

lemma persistence_patch_neighbourhood_isOpen {X ι : Type*} [TopologicalSpace X]
    (O : ι → Set X) (R : ι → C(X, X)) (hO : ∀ i, IsOpen (O i))
    (l : List ι) : IsOpen (persistencePatchNeighbourhood O R l) := by
  induction l with
  | nil => exact isOpen_empty
  | cons i l ih => exact (hO i).union (ih.preimage (R i).continuous)

lemma persistence_patch_neighbourhood_contains {X ι : Type*} [TopologicalSpace X]
    (A : Set X) (O : ι → Set X) (R : ι → C(X, X))
    (hR : ∀ i a, a ∈ A → R i a = a) (l : List ι) :
    ∀ a, a ∈ A → (∃ i ∈ l, a ∈ O i) → a ∈ persistencePatchNeighbourhood O R l := by
  induction l with
  | nil =>
    intro a ha h
    obtain ⟨i, hi, _⟩ := h
    cases hi
  | cons i l ih =>
    intro a ha h
    obtain ⟨k, hk, hak⟩ := h
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Or.inl hak
    · apply Or.inr
      change R i a ∈ persistencePatchNeighbourhood O R l
      rw [hR i a ha]
      exact ih a ha ⟨k, hk, hak⟩

lemma persistence_patch_neighbourhood_endpoint {X ι : Type*} [TopologicalSpace X]
    (A : Set X) (O : ι → Set X) (R : ι → C(X, X))
    (hR : ∀ i a, a ∈ A → R i a = a) (hret : ∀ i x, x ∈ O i → R i x ∈ A)
    (l : List ι) : ∀ x, x ∈ persistencePatchNeighbourhood O R l →
      persistencePatchComposite R l x ∈ A := by
  induction l with
  | nil => intro x hx; exact False.elim hx
  | cons i l ih =>
    intro x hx
    change persistencePatchComposite R l (R i x) ∈ A
    rcases hx with hx | hx
    · rw [persistence_patch_composite_fixed A R hR l (R i x) (hret i x hx)]
      exact hret i x hx
    · exact ih (R i x) hx

end HodgeLean.Foundations.QuotientDuality
