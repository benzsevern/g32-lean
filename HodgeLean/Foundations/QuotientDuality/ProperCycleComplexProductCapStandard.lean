import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexProductCapCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedComplexNormalCapNormalization

/-! # Original ordinary complex product cap on the specified standard source
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original ordinary complex product normal cap sends the specified transported standard source to the specified transported tangential zero-section class.
Source: properCycle_complex_product_cap_coordinate_square; properCycle_iterated_complex_normal_cap_standard.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_product_cap_standard_source (r d : ℕ) :
    let Y := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))
    let U : Set Y := Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))
    let V : Set Y := {z | z.1 = 0}
    let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
      ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
    let a := normalizedRelativeCoclass (standardComplexLocalClassMul d) hz
    (properCycle_union_relative_support_cap Y U V (isClosed_singleton.preimage continuous_snd)
      (isClosed_eq continuous_fst continuous_const) (d*2) (r*2)
      (relativeCohomologyMap ℚ (d*2)
        (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0}) a)).hom
      (relativeHomologyMap ℚ (d*2+r*2)
        ((properCycle_iterated_support_intersection_pair_iso (TopCat.of (Fin d → ℂ)) {0} Set.univ (r*2)).inv ≫
          properCycle_complex_normal_product_intersection_pair_map r d)
        (properCycle_complex_normal_source_class d (r*2))) =
      relativeHomologyMap ℚ (r*2) (properCycle_complex_normal_product_tangent_pair_iso r d).hom
        (relativeHomologyDegreeCast (Nat.zero_add (r*2)) (properCycle_normal_zero_section_local_class d (r*2))) := by
  let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
    ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
  let a := normalizedRelativeCoclass (standardComplexLocalClassMul d) hz
  have hc : (properCycle_iterated_union_relative_cap (TopCat.of (Fin d → ℂ)) {0} Set.univ
      isClosed_singleton isClosed_univ (d*2) a (r*2)).hom
      (properCycle_complex_normal_source_class d (r*2)) =
      relativeHomologyDegreeCast (Nat.zero_add (r*2)) (properCycle_normal_zero_section_local_class d (r*2)) :=
    properCycle_iterated_complex_normal_cap_standard d (r*2)
  have h := properCycle_complex_product_cap_coordinate_square r d (d*2) a
    (properCycle_complex_normal_source_class d (r*2))
  rw [hc] at h
  exact h.symm

end HodgeLean.Foundations.QuotientDuality
