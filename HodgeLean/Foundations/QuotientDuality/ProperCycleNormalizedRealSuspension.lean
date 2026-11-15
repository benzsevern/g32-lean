import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineRightComparison

/-! # The normalized original real suspension map
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual real suspension map uses inverse original excision, the specified signed connecting map, and actual tangential projection. -/
def properCycle_normalized_real_suspension (d : ℕ) :
    RelativeHomology ℚ (properCycle_affine_suspension_pair d) (d+1) →ₗ[ℚ]
      RelativeHomology ℚ (puncturedPair ℝ d) d :=
  (relativeHomologyMap ℚ d (properCycle_real_equator_projection d)).comp
    (((properCycle_affine_half_ray_right_homology_iso d (d+1)).inv ≫
      (properCycle_affine_half_ray_shortExact d).δ (d+1) d (by simp) ≫
        HomologicalComplex.homologyMap (properCycle_affine_half_ray_left_iso d).hom d).hom)

/-- The actual real suspension sends the specified standard product local class to minus the original standard local class. -/
theorem properCycle_normalized_real_suspension_standard (d : ℕ) :
    properCycle_normalized_real_suspension d
      (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
        (standardLocalClass ℚ (d+1))) = -standardLocalClass ℚ d := by
  unfold properCycle_normalized_real_suspension
  change relativeHomologyMap ℚ d (properCycle_real_equator_projection d)
    ((HomologicalComplex.homologyMap (properCycle_affine_half_ray_left_iso d).hom d).hom
      (((properCycle_affine_half_ray_shortExact d).δ (d+1) d (by simp)).hom
        ((properCycle_affine_half_ray_right_homology_iso d (d+1)).inv.hom
          (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom
            (standardLocalClass ℚ (d+1)))))) = _
  rw [properCycle_affine_half_ray_inverse_standard]
  exact properCycle_affine_half_ray_connecting_standard d

/-- Ordered real coordinates give the original suspension map between the specified coordinate-space local groups. -/
def properCycle_ordered_real_suspension (d : ℕ) :
    RelativeHomology ℚ (puncturedPair ℝ (d+1)) (d+1) →ₗ[ℚ]
      RelativeHomology ℚ (puncturedPair ℝ d) d :=
  (properCycle_normalized_real_suspension d).comp
    (relativeHomologyMap ℚ (d+1) (properCycle_real_suspension_pair_iso d).hom)

/-- The ordered coordinate suspension retains the actual negative standard local coefficient. -/
theorem properCycle_ordered_real_suspension_standard (d : ℕ) :
    properCycle_ordered_real_suspension d (standardLocalClass ℚ (d+1)) =
      -standardLocalClass ℚ d := properCycle_normalized_real_suspension_standard d

/-- Two successive original real suspensions retain the original positive unit local coefficient. -/
theorem properCycle_ordered_double_real_suspension_standard (d : ℕ) :
    properCycle_ordered_real_suspension d
      (properCycle_ordered_real_suspension (d+1) (standardLocalClass ℚ (d+2))) =
      standardLocalClass ℚ d := by
  rw [properCycle_ordered_real_suspension_standard, map_neg,
    properCycle_ordered_real_suspension_standard, neg_neg]

end HodgeLean.Foundations.QuotientDuality
