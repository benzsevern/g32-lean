import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCollar

/-! # Literal values of the retained retraction on original support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- At an actual neighborhood point lying on the original support, the retained retraction has precisely that original ambient value.
Source: ProperCycleSupportCollar.inclusion_factor; ProperCycleSupportCollar.inclusion_retraction.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.retraction_on_support
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (u : C.neighborhood) (hu : u.val ∈ S) : (C.retraction u).val = u.val := by
  let s : S := ⟨u.val, hu⟩
  have hj : C.inclusion s = u := by
    apply Subtype.ext
    have h := ConcreteCategory.congr_hom C.inclusion_factor (s : TopCat.of S)
    exact h
  have hr : C.retraction u = s := by
    rw [← hj]
    exact ConcreteCategory.congr_hom C.inclusion_retraction s
  exact congrArg Subtype.val hr

end HodgeLean.Foundations.QuotientDuality
