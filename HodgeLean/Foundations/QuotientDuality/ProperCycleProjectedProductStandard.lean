import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedProductCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleProductCapPointSource
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexProductCapStandard
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalTargetClass

/-! # Original projected product cap on the actual specified point source
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual projected ordinary product cap sends the specified actual point-source class to the original intrinsic standard complex class.
Source: properCycle_complex_product_cap_standard_source; properCycle_complex_normal_target_standard_class; properCycle_complex_product_cap_point_source.
HC no distance; AV milestone no distance. -/
theorem properCycle_projected_product_standard (r d : ℕ) :
    let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
      ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
    properCycle_product_projected_support_cap (Fin r → ℂ) (Fin d → ℂ) (d*2) (r*2)
      (normalizedRelativeCoclass (standardComplexLocalClassMul d) hz)
      (relativeHomologyMap ℚ (d*2+r*2) (properCycle_complex_normal_product_point_pair_iso r d).hom
        (properCycle_complex_normal_source_class d (r*2))) =
      standardComplexLocalClassMul r := by
  let J := properCycle_product_support_point_pair_iso (Fin r → ℂ) (Fin d → ℂ)
  let M := (properCycle_iterated_support_intersection_pair_iso (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)).inv ≫
    properCycle_complex_normal_product_intersection_pair_map r d
  have hp : (properCycle_complex_normal_product_point_pair_iso r d).hom ≫ J.inv = M := by
    rw [← properCycle_complex_product_cap_point_source]
    simp only [J, M, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc := properCycle_complex_product_cap_standard_source r d
  have ht := properCycle_complex_normal_target_standard_class r d
  rw [properCycle_product_tangent_local_homology_projection] at ht
  have hs : relativeHomologyMap ℚ (d*2+r*2) J.inv
      (relativeHomologyMap ℚ (d*2+r*2) (properCycle_complex_normal_product_point_pair_iso r d).hom
        (properCycle_complex_normal_source_class d (r*2))) =
      relativeHomologyMap ℚ (d*2+r*2) M (properCycle_complex_normal_source_class d (r*2)) := by
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hp]
  dsimp only [properCycle_product_projected_support_cap, LinearMap.comp_apply]
  rw [hs]
  rw [hc]
  exact ht

end HodgeLean.Foundations.QuotientDuality
