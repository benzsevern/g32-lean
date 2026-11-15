import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSourceExcision
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedProductCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeIso
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexLocalCap

/-! # Original frozen local cap through actual projected support coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The frozen original complex local cap is the actual projected support cap, retaining its specified normal coclass and ambient degree transport.
Source: properCycle_standard_complex_local_cap; properCycle_product_source_excision; properCycle_product_tangent_local_homology_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_original_projected_cap (r d : ℕ)
    (z : orientationGroup (TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (2*(r+d)) (0,0)) :
    properCycle_standard_complex_local_cap r d z =
      properCycle_product_projected_support_cap (Fin r → ℂ) (Fin d → ℂ) (2*d) (2*r)
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
          (standardComplexLocalClass_ne_zero_for_chart d))
        (relativeHomologyDegreeCast (show 2*(r+d)=2*d+2*r by omega) z) := by
  unfold properCycle_standard_complex_local_cap
  dsimp only
  rw [properCycle_product_source_excision, properCycle_product_tangent_local_homology_projection]
  dsimp only [Iso.trans_inv, LinearMap.comp_apply]
  rw [properCycle_relative_degree_iso_apply]
  rfl

end HodgeLean.Foundations.QuotientDuality
