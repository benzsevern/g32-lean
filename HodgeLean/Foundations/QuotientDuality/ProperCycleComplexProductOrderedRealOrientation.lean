import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexProductCoordinateOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexBlockCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeTransport

/-! # Frozen product orientation in the specified ordered real block coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The frozen original product orientation is the specified standard real local class in consecutive complex real coordinates followed by the literal complex block split, with its original degree transport.
Source: properCycle_complex_product_orientation_coordinates; properCycle_relative_homology_degree_map; standardComplexLocalClass.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_product_ordered_real_orientation (r d : ℕ) :
    let E := properCycle_complex_product_coordinate_pair_iso r d
      (properCycle_complex_block_coordinates r d).symm
    properCycle_complex_product_standard_orientation r d =
      relativeHomologyDegreeCast (Nat.mul_comm (r+d) 2)
        (relativeHomologyMap ℚ ((r+d)*2)
          ((standardComplexRealPairIso (r+d)).inv ≫ E.inv) (standardLocalClass ℚ ((r+d)*2))) := by
  let E := properCycle_complex_product_coordinate_pair_iso r d
    (properCycle_complex_block_coordinates r d).symm
  rw [properCycle_complex_product_orientation_coordinates r d (properCycle_complex_block_coordinates r d).symm]
  change relativeHomologyMap ℚ (2*(r+d)) E.inv
      (relativeHomologyDegreeCast (Nat.mul_comm (r+d) 2)
        (relativeHomologyMap ℚ ((r+d)*2) (standardComplexRealPairIso (r+d)).inv
          (standardLocalClass ℚ ((r+d)*2)))) = _
  rw [properCycle_relative_homology_degree_map]
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply]
  rfl

end HodgeLean.Foundations.QuotientDuality
