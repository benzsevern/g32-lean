import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalSourcePair
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeComposition
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalProductPairs
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealDimensionPairs
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedBaseIdentities
import HodgeLean.Foundations.QuotientDuality.ProperCycleTopPairAmbientExt
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexProductOrderedRealOrientation

/-! # Specified original normal source coordinates on actual relative pairs
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual relative point-pair map of the specified normal-cap source is the original consecutive complex real inverse followed by the literal complex block split, including the real dimension pair transport.
Source: properCycle_mixed_complex_real_coordinates; properCycle_real_dimension_pair_coordinates; properCycle_iterated_real_base_map_id; properCycle_top_pair_hom_ext.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_source_pair_coordinates (r d : ℕ) :
    let e : (r+d)*2 = d*2+r*2 := by omega
    (properCycle_real_dimension_pair_iso e).hom ≫ properCycle_complex_normal_source_pair_map d (r*2) ≫
      (properCycle_complex_normal_product_point_pair_iso r d).hom =
      (standardComplexRealPairIso (r+d)).inv ≫
        (properCycle_complex_product_coordinate_pair_iso r d (properCycle_complex_block_coordinates r d).symm).inv := by
  let e : (r+d)*2 = d*2+r*2 := by omega
  apply properCycle_top_pair_hom_ext
  ext z
  change properCycle_complex_normal_product_coordinates r d
      (properCycle_iterated_real_base_map (𝟙 (TopCat.of (Fin d → ℂ))) (r*2)
        (properCycle_iterated_real_local_coordinates d (r*2)
          (TopPair.Hom.fst (properCycle_real_dimension_pair_iso e).hom z))) =
    properCycle_complex_block_coordinates r d ((Complex.piCoordCLE (r+d)).symm z)
  rw [properCycle_iterated_real_base_map_id]
  change properCycle_complex_normal_product_coordinates r d
      (properCycle_iterated_real_local_coordinates d (r*2)
        (TopPair.Hom.fst (properCycle_real_dimension_pair_iso e).hom z)) = _
  rw [properCycle_real_dimension_pair_coordinates]
  exact (properCycle_mixed_complex_real_coordinates r d z).symm

/-- The specified source class in the actual normal-cap computation is the frozen original complex product orientation after its actual point-pair map and original ambient-degree transport.
Source: properCycle_complex_normal_source_pair_coordinates; properCycle_real_dimension_standard_class; properCycle_complex_product_ordered_real_orientation.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_source_orientation (r d : ℕ) :
    relativeHomologyDegreeCast (show d*2+r*2 = 2*(r+d) by omega)
      (relativeHomologyMap ℚ (d*2+r*2) (properCycle_complex_normal_product_point_pair_iso r d).hom
        (properCycle_complex_normal_source_class d (r*2))) =
      properCycle_complex_product_standard_orientation r d := by
  let e : (r+d)*2 = d*2+r*2 := by omega
  let h : d*2+r*2 = 2*(r+d) := by omega
  let M := properCycle_complex_normal_source_pair_map d (r*2) ≫
    (properCycle_complex_normal_product_point_pair_iso r d).hom
  let B := (standardComplexRealPairIso (r+d)).inv ≫
    (properCycle_complex_product_coordinate_pair_iso r d (properCycle_complex_block_coordinates r d).symm).inv
  have hp := properCycle_complex_normal_source_pair_coordinates r d
  change (properCycle_real_dimension_pair_iso e).hom ≫ M = B at hp
  have hm := congrArg (fun f => relativeHomologyMap ℚ ((r+d)*2) f (standardLocalClass ℚ ((r+d)*2))) hp
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hm
  have hc : relativeHomologyMap ℚ (d*2+r*2) (properCycle_complex_normal_product_point_pair_iso r d).hom
      (properCycle_complex_normal_source_class d (r*2)) =
      relativeHomologyMap ℚ (d*2+r*2) M (standardLocalClass ℚ (d*2+r*2)) := by
    rw [properCycle_complex_normal_source_class_pair]
    simp only [M, relativeHomologyMap_comp, LinearMap.comp_apply]
  change relativeHomologyDegreeCast h
    (relativeHomologyMap ℚ (d*2+r*2) (properCycle_complex_normal_product_point_pair_iso r d).hom
      (properCycle_complex_normal_source_class d (r*2))) = _
  rw [hc, ← properCycle_real_dimension_standard_class e,
    properCycle_relative_homology_degree_map, properCycle_relative_degree_cast_trans, hm]
  exact (properCycle_complex_product_ordered_real_orientation r d).symm

end HodgeLean.Foundations.QuotientDuality
