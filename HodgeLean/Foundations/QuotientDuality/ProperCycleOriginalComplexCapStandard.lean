import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalProjectedCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedProductStandard
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedProductDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCoclassDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalSourceCoordinates

/-! # Original complex normal cap on its frozen standard product orientation
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The frozen original complex normal cap sends its specified original complex product orientation to the specified intrinsic complex standard local class.
Source: properCycle_original_projected_cap; properCycle_projected_product_standard; properCycle_complex_normal_source_orientation; properCycle_complex_coclass_degree.
HC no distance; AV milestone no distance. -/
theorem properCycle_original_complex_cap_standard (r d : ℕ) :
    properCycle_standard_complex_local_cap r d (properCycle_complex_product_standard_orientation r d) =
      standardComplexLocalClass ℚ r := by
  let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
    ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
  let a := normalizedRelativeCoclass (standardComplexLocalClassMul d) hz
  let w := relativeHomologyMap ℚ (d*2+r*2) (properCycle_complex_normal_product_point_pair_iso r d).hom
    (properCycle_complex_normal_source_class d (r*2))
  have hs : properCycle_product_projected_support_cap (Fin r → ℂ) (Fin d → ℂ) (d*2) (r*2) a w =
      standardComplexLocalClassMul r := properCycle_projected_product_standard r d
  have ht := properCycle_projected_product_degree (Fin r → ℂ) (Fin d → ℂ)
    (Nat.mul_comm d 2) (Nat.mul_comm r 2) a w
  have ha : (Nat.mul_comm d 2 ▸ a) = normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
      (standardComplexLocalClass_ne_zero_for_chart d) := properCycle_complex_coclass_degree d
  rw [hs, ha] at ht
  rw [properCycle_original_projected_cap]
  have ho : relativeHomologyDegreeCast (show d*2+r*2=2*(r+d) by omega) w =
      properCycle_complex_product_standard_orientation r d := properCycle_complex_normal_source_orientation r d
  rw [← ho, properCycle_relative_degree_cast_trans]
  exact ht.symm

end HodgeLean.Foundations.QuotientDuality
