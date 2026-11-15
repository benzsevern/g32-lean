import HodgeLean.Foundations.QuotientDuality.ProperCycleProductPointAmbient
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedIntersectionAmbient

/-! # Original complex cap source in literal point coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original recursive source intersection comparison and actual product support map give the specified actual complex point pair map.
Source: properCycle_product_support_point_ambient; properCycle_iterated_intersection_inverse_ambient; properCycle_top_pair_hom_ext.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_product_cap_point_source (r d : ℕ) :
    (properCycle_iterated_support_intersection_pair_iso (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)).inv ≫
      properCycle_complex_normal_product_intersection_pair_map r d ≫
        (properCycle_product_support_point_pair_iso (Fin r → ℂ) (Fin d → ℂ)).hom =
      (properCycle_complex_normal_product_point_pair_iso r d).hom := by
  apply properCycle_top_pair_hom_ext
  change TopPair.Hom.fst
      (properCycle_iterated_support_intersection_pair_iso (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)).inv ≫
    TopPair.Hom.fst (properCycle_complex_normal_product_intersection_pair_map r d) ≫
    TopPair.Hom.fst (properCycle_product_support_point_pair_iso (Fin r → ℂ) (Fin d → ℂ)).hom = _
  rw [properCycle_iterated_intersection_inverse_ambient, properCycle_product_support_point_ambient]
  ext z
  rfl

end HodgeLean.Foundations.QuotientDuality
