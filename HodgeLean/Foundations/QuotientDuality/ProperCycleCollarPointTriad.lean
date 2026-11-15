import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointPair

/-! # The literal point complement in a retained support collar
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The two actual collar subspaces used for the local support cap have union precisely the complement of the retained support point.
Source: ProperCycleSupportCollar.inclusion_factor; ProperCycleSupportCollar.inclusion_retraction.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.point_triad_union {X : TopCat.{0}} {S : Set X}
    (C : ProperCycleSupportCollar X S) (z : S) :
    (Subtype.val ⁻¹' Sᶜ : Set C.neighborhood) ∪
        (C.retraction ⁻¹' ({z} : Set S)ᶜ) =
      ({C.inclusion z} : Set C.neighborhood)ᶜ := by
  have hj (s : S) : (C.inclusion s).val = s.val := by
    have h := ConcreteCategory.congr_hom C.inclusion_factor (s : TopCat.of S)
    exact h
  have hr (s : S) : C.retraction (C.inclusion s) = s :=
    ConcreteCategory.congr_hom C.inclusion_retraction s
  ext u
  change (u.val ∉ S ∨ C.retraction u ≠ z) ↔ u ≠ C.inclusion z
  constructor
  · rintro (hu | hu) he
    · subst u
      exact hu ((hj z).symm ▸ z.property)
    · subst u
      exact hu (hr z)
  · intro hu
    by_cases hs : u.val ∈ S
    · right
      intro hz
      apply hu
      let s : S := ⟨u.val, hs⟩
      have hju : C.inclusion s = u := Subtype.ext (hj s)
      have hru : C.retraction u = s := by rw [← hju, hr]
      exact hju.symm.trans (congrArg C.inclusion (hru.symm.trans hz))
    · exact Or.inl hs

end HodgeLean.Foundations.QuotientDuality
