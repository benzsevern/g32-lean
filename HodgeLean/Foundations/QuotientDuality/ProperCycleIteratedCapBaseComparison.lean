import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedUnionRelativeCap

/-! # Original ordinary support cap at the base of the actual iteration
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- At the original base the actual iterated normal cap is the original ordinary intersection-support cap with its specified source excision.
Source: properCycle_iterated_union_relative_cap; properCycle_iterated_support_intersection_pair_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_union_relative_cap_zero
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (p : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    properCycle_iterated_union_relative_cap Y S T hS hT p a 0 =
      properCycle_union_relative_support_cap Y S T hS hT p 0 a := by
  have hJ : (properCycle_iterated_support_intersection_pair_iso Y S T 0).inv =
      𝟙 (TopPair.ofSubset (X := Y) (S ∩ T)ᶜ) := rfl
  dsimp only [properCycle_iterated_union_relative_cap, properCycle_real_support_space,
    properCycle_real_normal_support, properCycle_real_point_support, properCycle_real_support_coclass]
  erw [hJ, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  rfl

end HodgeLean.Foundations.QuotientDuality
