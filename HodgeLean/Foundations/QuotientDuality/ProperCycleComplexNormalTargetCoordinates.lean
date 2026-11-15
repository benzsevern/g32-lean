import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalTargetPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedBaseCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealDimensionPairs
import HodgeLean.Foundations.QuotientDuality.ProperCycleTopPairAmbientExt

/-! # Original intrinsic complex coordinates of the actual zero-section target
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual zero-section pair map followed by complex tangential coordinates and literal projection is the specified intrinsic complex real inverse, including the real dimension transport.
Source: properCycle_iterated_real_base_coordinates; properCycle_iterated_normal_coordinates_prefix; properCycle_real_dimension_pair_coordinates.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_target_pair_coordinates (r d : ℕ) :
    let e : r*2 = 0*2+r*2 := by omega
    (properCycle_real_dimension_pair_iso e).hom ≫ properCycle_complex_normal_target_pair_map r d =
      (standardComplexRealPairIso r).inv := by
  let e : r*2 = 0*2+r*2 := by omega
  apply properCycle_top_pair_hom_ext
  ext z
  change (Complex.piCoordCLE r).symm
      (properCycle_real_support_coordinates (TopCat.of (Fin d → ℂ)) (r*2)
        (properCycle_iterated_real_base_map (properCycle_normal_zero_base_map d) (r*2)
          (properCycle_iterated_real_local_coordinates 0 (r*2)
            (TopPair.Hom.fst (properCycle_real_dimension_pair_iso e).hom z)))).1 =
    (Complex.piCoordCLE r).symm z
  rw [properCycle_iterated_real_base_coordinates]
  apply congrArg (Complex.piCoordCLE r).symm
  funext i
  rw [properCycle_iterated_normal_coordinates_prefix, properCycle_real_dimension_pair_coordinates]

end HodgeLean.Foundations.QuotientDuality
