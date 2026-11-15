import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseComplement

/-! Quotients of actual neighbourhoods inside the ambient collapse. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The quotient projection restricted to the specified neighbourhood. -/
def persistenceCollapseNeighbourhoodProjection
    {X : Type*} [TopologicalSpace X] (A U : Set X) :
    C(U, ((Quotient.mk (persistenceCollapseSetoid A)) '' U)) :=
  ⟨fun u => ⟨Quotient.mk (persistenceCollapseSetoid A) u.val,
    ⟨u.val, u.property, rfl⟩⟩,
    (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _⟩

lemma persistence_collapse_neighbourhood_projection_isQuotientMap
    {X : Type*} [TopologicalSpace X] (A U : Set X) (hA : IsClosed A)
    (hAU : A ⊆ U) : IsQuotientMap (persistenceCollapseNeighbourhoodProjection A U) := by
  let q := Quotient.mk (persistenceCollapseSetoid A)
  let e : U ≃ₜ (q ⁻¹' (q '' U)) :=
    Homeomorph.setCongr (persistence_collapse_neighbourhood_preimage A U hAU).symm
  have heq : (persistenceCollapseNeighbourhoodProjection A U : U → (q '' U)) =
      (q '' U).restrictPreimage q ∘ e := rfl
  have hc : IsClosedMap (persistenceCollapseNeighbourhoodProjection A U) := by
    rw [heq]
    exact ((persistence_collapse_isClosedMap A hA).restrictPreimage (q '' U)).comp
      e.isHomeomorph.isClosedMap
  apply hc.isQuotientMap (persistenceCollapseNeighbourhoodProjection A U).continuous
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The induced map from the neighbourhood collapse into the ambient quotient image. -/
def persistenceCollapseNeighbourhoodMap
    {X : Type*} [TopologicalSpace X] (A U : Set X) :
    Quotient (persistenceCollapseSetoid {u : U | u.val ∈ A}) →
      ((Quotient.mk (persistenceCollapseSetoid A)) '' U) :=
  Quotient.lift (persistenceCollapseNeighbourhoodProjection A U) (by
    rintro u v (rfl | ⟨hu, hv⟩)
    · rfl
    · exact Subtype.ext (Quotient.sound (Or.inr ⟨hu, hv⟩)))

lemma persistence_collapse_neighbourhood_map_isHomeomorph
    {X : Type*} [TopologicalSpace X] (A U : Set X) (hA : IsClosed A)
    (hAU : A ⊆ U) : IsHomeomorph (persistenceCollapseNeighbourhoodMap A U) := by
  have hq : IsQuotientMap (persistenceCollapseNeighbourhoodMap A U) :=
    IsQuotientMap.of_comp_of_isCoinducing
      (f := Quotient.mk (persistenceCollapseSetoid {u : U | u.val ∈ A}))
      (g := persistenceCollapseNeighbourhoodMap A U)
      (persistence_collapse_neighbourhood_projection_isQuotientMap A U hA hAU)
      isQuotientMap_quotient_mk'.isCoinducing
  apply isHomeomorph_iff_isQuotientMap_injective.mpr
  refine ⟨hq, ?_⟩
  intro a b
  induction a using Quotient.inductionOn with | h u =>
    induction b using Quotient.inductionOn with | h v =>
      intro heq
      have heq' : Quotient.mk (persistenceCollapseSetoid A) u.val =
          Quotient.mk (persistenceCollapseSetoid A) v.val := congrArg Subtype.val heq
      apply Quotient.sound
      rcases (persistence_collapse_eq_iff A u.val v.val).mp heq' with heq' | huv
      · exact Or.inl (Subtype.ext heq')
      · exact Or.inr huv

end HodgeLean.Foundations.QuotientDuality
