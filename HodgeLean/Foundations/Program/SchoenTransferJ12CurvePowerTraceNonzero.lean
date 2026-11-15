import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerTopCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Any actual top coordinate detects the normalized ordered curve-power top cup.
Source: the nonzero actual Künneth top cup and injectivity of the specified coordinate. -/
theorem s4_selected_curve_power_top_trace_ne_zero
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (J : HQ (g3_power Y n) (2 * n) ≃ₗ[ℚ] ℚ) :
    J (s4_selected_divisor_cup (g3_power Y n) n
      (fun i => homPullback (g3_proj Y n i) 2 (I.symm 1))) ≠ 0 := by
  intro h
  apply s4_selected_curve_power_top_cup_ne_zero Y hdim I n
  exact J.injective (h.trans (map_zero J).symm)

#print axioms s4_selected_curve_power_top_trace_ne_zero
end HodgeLean.Foundations.Program
