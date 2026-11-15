import HodgeLean.Foundations.Program.RelativeFrameOperatorDefs

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

def rf4_inverseAnnulus (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    b63r_bddHol (b63r_annulus n r) :=
  rf4_bddOn (rf4_closedAnnulus_isCompact hn r) (rf4_annulus_subset_closed n r)
    (fun u ↦ u⁻¹)
    (fun _ hu ↦ ((differentiableAt_id (𝕜 := ℂ)).inv (rf4_closedAnnulus_ne_zero hn hr hu)).continuousAt.continuousWithinAt)
    (fun _ hu ↦ ((differentiableAt_id (𝕜 := ℂ)).inv
      (rf4_closedAnnulus_ne_zero hn hr (rf4_annulus_subset_closed n r hu))).differentiableWithinAt)

theorem rf4_inverse_circle_integral (ρ : ℝ) (hρ : 0 < ρ) :
    (∮ z in C((0 : ℂ), ρ), z⁻¹) = 2 * Real.pi * Complex.I := by
  simpa only [sub_zero] using
    (circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := 0) (R := ρ)
      (by simpa only [Metric.mem_ball, dist_self] using hρ))

end HodgeLean.Foundations.Program
