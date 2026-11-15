import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalTargetCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeComposition

/-! # Specified intrinsic complex class through the original tangential contraction
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original tangential contraction of the specified normal zero-section class is its original standard real class carried by the actual intrinsic target pair map, retaining the source degree transport.
Source: properCycle_product_tangent_local_homology_projection; properCycle_relative_homology_degree_map; properCycle_complex_normal_target_pair_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_target_class_pair (r d : ℕ) :
    (properCycle_product_tangent_local_homology_iso (Fin r → ℂ) (Fin d → ℂ) (r*2)).hom.hom
      (relativeHomologyMap ℚ (r*2) (properCycle_complex_normal_product_tangent_pair_iso r d).hom
        (relativeHomologyDegreeCast (Nat.zero_add (r*2)) (properCycle_normal_zero_section_local_class d (r*2)))) =
      relativeHomologyDegreeCast (Nat.zero_add (r*2))
        (relativeHomologyMap ℚ (0+r*2) (properCycle_complex_normal_target_pair_map r d)
          (standardLocalClass ℚ (0+r*2))) := by
  rw [properCycle_product_tangent_local_homology_projection]
  change relativeHomologyMap ℚ (r*2) (properCycle_product_tangent_projection_pair (Fin r → ℂ) (Fin d → ℂ))
    (relativeHomologyMap ℚ (r*2) (properCycle_complex_normal_product_tangent_pair_iso r d).hom
      (relativeHomologyDegreeCast (Nat.zero_add (r*2)) (properCycle_normal_zero_section_local_class d (r*2)))) = _
  simp only [properCycle_relative_homology_degree_map]
  simp only [properCycle_complex_normal_target_pair_map, relativeHomologyMap_comp,
    LinearMap.comp_apply, properCycle_normal_zero_section_local_class, properCycle_iterated_real_local_class]

/-- The original frozen tangential contraction sends the specified actual zero-section target class to the specified intrinsic standard complex local class in its original uncast degree.
Source: properCycle_complex_normal_target_class_pair; properCycle_complex_normal_target_pair_coordinates; properCycle_real_dimension_standard_class.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_target_standard_class (r d : ℕ) :
    (properCycle_product_tangent_local_homology_iso (Fin r → ℂ) (Fin d → ℂ) (r*2)).hom.hom
      (relativeHomologyMap ℚ (r*2) (properCycle_complex_normal_product_tangent_pair_iso r d).hom
        (relativeHomologyDegreeCast (Nat.zero_add (r*2)) (properCycle_normal_zero_section_local_class d (r*2)))) =
      standardComplexLocalClassMul r := by
  rw [properCycle_complex_normal_target_class_pair]
  let e : r*2 = 0*2+r*2 := by omega
  let h : 0*2+r*2 = r*2 := by omega
  have hp := properCycle_complex_normal_target_pair_coordinates r d
  change (properCycle_real_dimension_pair_iso e).hom ≫ properCycle_complex_normal_target_pair_map r d =
    (standardComplexRealPairIso r).inv at hp
  have hm := congrArg (fun f => relativeHomologyMap ℚ (r*2) f (standardLocalClass ℚ (r*2))) hp
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hm
  change relativeHomologyDegreeCast h
    (relativeHomologyMap ℚ (0*2+r*2) (properCycle_complex_normal_target_pair_map r d)
      (standardLocalClass ℚ (0*2+r*2))) = _
  rw [← properCycle_real_dimension_standard_class e,
    properCycle_relative_homology_degree_map, properCycle_relative_degree_cast_trans]
  change relativeHomologyMap ℚ (r*2) (properCycle_complex_normal_target_pair_map r d)
    (relativeHomologyMap ℚ (r*2) (properCycle_real_dimension_pair_iso e).hom
      (standardLocalClass ℚ (r*2))) = _
  exact hm

end HodgeLean.Foundations.QuotientDuality
