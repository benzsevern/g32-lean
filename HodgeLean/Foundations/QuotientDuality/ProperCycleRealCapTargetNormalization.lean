import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapInverseSquare
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedRealSuspension

/-! # Original point-support normalization of the actual cap target suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual inverse target connecting map used by the cap lifts the specified negative equatorial class to the original standard product local class.
Source: properCycle_affine_half_ray_connecting_value; properCycle_affine_half_ray_inverse_standard.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_target_inverse_standard (d : ℕ) :
    (properCycle_real_cap_target_connecting_iso (TopCat.of (Fin d → ℝ)) {0} isClosed_singleton d).inv.hom
      (((properCycle_affine_half_ray_left_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₁.homologyπ d).hom) 1) =
      (properCycle_affine_half_ray_right_homology_iso d (d+1)).inv.hom
        (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
          (standardLocalClass ℚ (d+1))) := by
  let e := properCycle_real_cap_target_connecting_iso (TopCat.of (Fin d → ℝ)) {0} isClosed_singleton d
  have h := ConcreteCategory.congr_hom (properCycle_affine_half_ray_connecting_value d) 1
  change e.hom.hom (((properCycle_affine_half_ray_right_cycle d ≫
      (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1)).hom) 1) =
    (((properCycle_affine_half_ray_left_cycle d ≫
      (properCycle_affine_half_ray_sequence d).X₁.homologyπ d).hom) 1) at h
  calc
    _ = e.inv.hom (e.hom.hom (((properCycle_affine_half_ray_right_cycle d ≫
      (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1)).hom) 1)) :=
      congrArg e.inv.hom h.symm
    _ = _ := ConcreteCategory.congr_hom e.hom_inv_id _
    _ = _ := (properCycle_affine_half_ray_inverse_standard d).symm

end HodgeLean.Foundations.QuotientDuality
