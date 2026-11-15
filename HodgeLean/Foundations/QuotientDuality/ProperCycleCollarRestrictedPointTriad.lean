import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRetractionOnSupport

/-! # Literal point-triad unions on an actual smaller collar neighborhood
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Restricting the collar to an actual neighborhood of the retained support point keeps its literal point-complement union.
Source: ProperCycleSupportCollar.retraction_on_support; subspace extensionality.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.restricted_point_triad_union
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (W : Opens X) (hWN : (W : Set X) ⊆ C.neighborhood) (z : S) (hzW : z.val ∈ W) :
    (Subtype.val ⁻¹' Sᶜ : Set W) ∪
        ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' ({z} : Set S)ᶜ) =
      ({⟨z.val, hzW⟩} : Set W)ᶜ := by
  ext x
  change (x.val ∉ S ∨ C.retraction ⟨x.val, hWN x.property⟩ ≠ z) ↔ x ≠ ⟨z.val, hzW⟩
  have hr (hs : x.val ∈ S) : (C.retraction ⟨x.val, hWN x.property⟩).val = x.val :=
    C.retraction_on_support _ hs
  constructor
  · rintro (hs | he) hx
    · exact hs ((congrArg Subtype.val hx).symm ▸ z.property)
    · apply he
      apply Subtype.ext
      exact (hr ((congrArg Subtype.val hx).symm ▸ z.property)).trans (congrArg Subtype.val hx)
  · intro hx
    by_cases hs : x.val ∈ S
    · right
      intro he
      apply hx
      exact Subtype.ext ((hr hs).symm.trans (congrArg Subtype.val he))
    · exact Or.inl hs

end HodgeLean.Foundations.QuotientDuality
