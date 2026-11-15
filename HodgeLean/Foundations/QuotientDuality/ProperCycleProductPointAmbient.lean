import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupportPointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexProductCapCoordinates

/-! # Literal ambient maps in original product support comparisons
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original product support-to-point pair isomorphism retains the literal identity ambient map.
Source: properCycle_product_support_point_pair_iso; properCycle_subset_eq_pair_ambient.
HC no distance; AV milestone no distance. -/
theorem properCycle_product_support_point_ambient
    (E F : Type) [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F] :
    TopPair.Hom.fst (properCycle_product_support_point_pair_iso E F).hom = 𝟙 (TopCat.of (E × F)) := by
  change (𝟙 (TopCat.of (E × F))) ≫ TopPair.Hom.fst
    (eqToIso (congrArg (fun A : Set (E × F) => TopPair.ofSubset (X := TopCat.of (E × F)) A)
      (properCycle_product_puncture_union E F))).hom = _
  rw [properCycle_subset_eq_pair_ambient _ _ _ (properCycle_product_puncture_union E F), Category.id_comp]

end HodgeLean.Foundations.QuotientDuality
