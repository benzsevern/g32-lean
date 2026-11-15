import HodgeLean.Foundations.Program.SchoenTransferJ12MixedSumAction
import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerKernelSpan
import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerTraceNonzero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Actual mixed retraction data reflect cycles through the actual even generating sum.
Source: cycle preservation of the actual product kernel and its nonzero sum-action scalar. -/
theorem s4_selected_sum_reflection_from_mixed_data
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (ha : 1 ≤ TopologicalSpace.dim A.left) (hdim : TopologicalSpace.dim Y.left = 1)
    (f g : Y ⟶ A) (k : ℕ)
    [IsIntegral (g3_power Y (2 * k)).left] [Smooth (g3_power Y (2 * k)).hom]
    [IsProjective (g3_power Y (2 * k)).hom]
    (IY : HQ Y 2 ≃ₗ[ℚ] ℚ) (IT : HQ (g3_power Y (2 * k)) (2 * (2 * k)) ≃ₗ[ℚ] ℚ)
    (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1) (c : ℚ) (hc : c ≠ 0)
    (hact : (s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
      (s4_selected_curve_mixed_divisor A Y g pol)).comp (homPullback f 1) = c • LinearMap.id)
    (x : HQ A (2 * k))
    (hx : homPullback (s4_sum f (2 * k)) (2 * k) x ∈ cfd_cycleSpan (g3_power Y (2 * k)) k) :
    x ∈ cfd_cycleSpan A k := by
  let t := IT (s4_selected_divisor_cup (g3_power Y (2 * k)) (2 * k)
    (fun i => homPullback (g3_proj Y (2 * k) i) 2 (IY.symm 1)))
  let s := (t * c ^ (2 * k)) * (Nat.factorial (2 * k) : ℚ)
  have ht : t ≠ 0 := s4_selected_curve_power_top_trace_ne_zero Y hdim IY (2 * k) IT
  have hs : s ≠ 0 := mul_ne_zero (mul_ne_zero ht (pow_ne_zero _ hc))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hcycle := s4_selected_curve_power_kernel_span A Y (TopologicalSpace.dim A.left)
    rfl ha hdim k IT g pol hpol (homPullback (s4_sum f (2 * k)) (2 * k) x) hx
  have hsum := LinearMap.congr_fun
    (s4_selected_mixed_sum_action A Y hdim f g (2 * k) IY IT pol c hc hact) x
  change s4_selected_corr_action A (g3_power Y (2 * k)) (2 * k) IT (2 * k)
    (2 * k) (2 * k) _ _ (homPullback (s4_sum f (2 * k)) (2 * k) x) = s • x at hsum
  rw [hsum] at hcycle
  have hnorm := Submodule.smul_mem (cfd_cycleSpan A k) s⁻¹ hcycle
  simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using hnorm

#print axioms s4_selected_sum_reflection_from_mixed_data
end HodgeLean.Foundations.Program
