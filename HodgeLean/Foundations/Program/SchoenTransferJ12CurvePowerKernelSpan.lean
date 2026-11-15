import HodgeLean.Foundations.Program.SchoenTransferJ12MixedKernelActionSpan

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The actual product kernel on a curve power preserves middle-degree cycles.
Source: the mixed divisor product action through the actual abelian power of the target. -/
theorem s4_selected_curve_power_kernel_span
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : ℕ) (hA : TopologicalSpace.dim A.left = a) (ha : 1 ≤ a)
    (hY : TopologicalSpace.dim Y.left = 1) (k : ℕ)
    (I : HQ (g3_power Y (2 * k)) (2 * (2 * k)) ≃ₗ[ℚ] ℚ)
    (f : Y ⟶ A) (pol : HQ A 2) (hpol : pol ∈ cfd_cycleSpan A 1)
    (b : HQ (g3_power Y (2 * k)) (2 * k))
    (hb : b ∈ cfd_cycleSpan (g3_power Y (2 * k)) k) :
    s4_selected_corr_action A (g3_power Y (2 * k)) (2 * k) I (2 * k)
      (2 * k) (2 * k) (by omega)
      (s4_selected_mixed_divisor_kernel A (g3_power Y (2 * k)) (2 * k)
        (fun i => g3_proj Y (2 * k) i ≫ f) pol) b ∈ cfd_cycleSpan A k := by
  have hdim : TopologicalSpace.dim (g3_power Y (2 * k)).left = 2 * k := by
    letI : SmoothOfRelativeDimension 1 Y.hom := by
      have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
      rwa [hY] at h
    letI : SmoothOfRelativeDimension (2 * k) (g3_power Y (2 * k)).hom := by
      simpa using spec_g3_smoothOfRelativeDimension_power Y 1 (2 * k)
    exact SmoothOfRelativeDimension.dim_eq (f := (g3_power Y (2 * k)).hom) (2 * k)
  have hlarge : 2 * k ≤ 2 * k * a + k := by
    have h := Nat.mul_le_mul_left (2 * k) ha
    omega
  exact s4_selected_mixed_divisor_kernel_action_span A (g3_power Y (2 * k)) a (2 * k)
    hA hdim (2 * k) k k (by omega) hlarge I
    (fun i => g3_proj Y (2 * k) i ≫ f) pol hpol b hb

#print axioms s4_selected_curve_power_kernel_span
end HodgeLean.Foundations.Program
