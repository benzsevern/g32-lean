import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalProductPairs
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalZeroSectionSuspension
import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentProjectionComparison

/-! # Actual pair map of the specified normal zero-section target class
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual normal zero-section local pair map followed by the original complex tangential coordinates and literal first projection.
Source: properCycle_normal_zero_section_local_class; properCycle_complex_normal_product_tangent_pair_iso; properCycle_product_tangent_projection_pair.
HC no distance; AV milestone no distance. -/
def properCycle_complex_normal_target_pair_map (r d : ℕ) :
    puncturedPair ℝ (0*2+r*2) ⟶ puncturedPair ℂ r :=
  (properCycle_iterated_real_local_pair_iso 0 (r*2)).hom ≫
    TopPair.ofSubsetHom (properCycle_iterated_real_base_map (properCycle_normal_zero_base_map d) (r*2))
      (properCycle_iterated_real_point_complement_map (properCycle_normal_zero_base_map d)
        {0} Set.univ (properCycle_normal_zero_base_complement d) (r*2)) ≫
    (properCycle_complex_normal_product_tangent_pair_iso r d).hom ≫
    properCycle_product_tangent_projection_pair (Fin r → ℂ) (Fin d → ℂ)

end HodgeLean.Foundations.QuotientDuality
