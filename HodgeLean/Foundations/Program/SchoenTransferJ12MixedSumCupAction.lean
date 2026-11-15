import HodgeLean.Foundations.Program.SchoenTransferJ12MixedKernelAssignmentZero
import HodgeLean.Foundations.Program.SchoenTransferJ12MixedKernelOneCup
import HodgeLean.Foundations.Program.SchoenTransferJ12TensorCupScalar
import HodgeLean.Foundations.Program.SchoenTransferJ12SumActionNormalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual mixed product kernel retracts sum pullback on cups with its exact nonnormalized scalar.
Source: actual repeated-assignment vanishing, factorwise kernel action and tensor alternation. -/
theorem s4_selected_mixed_sum_cup_action
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (f g : Y ⟶ A) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (IY : HQ Y 2 ≃ₗ[ℚ] ℚ) (IT : HQ (g3_power Y n) (2 * n) ≃ₗ[ℚ] ℚ)
    (pol : HQ A 2) (c : ℚ) (hc : c ≠ 0)
    (hact : (s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
      (s4_selected_curve_mixed_divisor A Y g pol)).comp (homPullback f 1) = c • LinearMap.id)
    (v : Fin n → HQ A 1) :
    s4_selected_corr_action A (g3_power Y n) n IT n n n (by omega)
      (s4_selected_mixed_divisor_kernel A (g3_power Y n) n
        (fun i => g3_proj Y n i ≫ g) pol)
      (homPullback (s4_sum f n) n ((cupProductOf A).cupMulti n v)) =
    ((IT (s4_selected_divisor_cup (g3_power Y n) n
      (fun i => homPullback (g3_proj Y n i) 2 (IY.symm 1))) * c ^ n) *
        (Nat.factorial n : ℚ)) • (cupProductOf A).cupMulti n v := by
  let H := s4_selected_corr_action A (g3_power Y n) n IT n n n (by omega)
    (s4_selected_mixed_divisor_kernel A (g3_power Y n) n
      (fun i => g3_proj Y n i ≫ g) pol)
  let R0 := s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
    (s4_selected_curve_mixed_divisor A Y g pol)
  let R := c⁻¹ • R0
  let t := IT (s4_selected_divisor_cup (g3_power Y n) n
    (fun i => homPullback (g3_proj Y n i) 2 (IY.symm 1)))
  have hR : R.comp (homPullback f 1) = LinearMap.id := by
    ext w
    change c⁻¹ • R0 (homPullback f 1 w) = w
    have hw := LinearMap.congr_fun hact w
    change R0 (homPullback f 1 w) = c • w at hw
    rw [hw, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hR0 : c • R = R0 := by
    dsimp only [R]
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hH : H.comp (s4_e1_oneCup Y n) = (t * c ^ n) •
      (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
        (PiTensorProduct.map (fun _ : Fin n => R)) := by
    have hh : H.comp (s4_e1_oneCup Y n) = t •
        (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
          (PiTensorProduct.map (fun _ : Fin n => R0)) :=
      s4_selected_mixed_kernel_oneCup A Y n IY IT g pol
    rw [← hR0, s4_selected_tensor_cup_scalar, smul_smul] at hh
    exact hh
  have hz (a : Fin n → Fin n) (ha : ¬ Function.Surjective a) (w : Fin n → HQ Y 1) :
      H ((cupProductOf (g3_power Y n)).cupMulti n
        (fun i => homPullback (g3_proj Y n (a i)) 1 (w i))) = 0 := by
    exact s4_selected_mixed_kernel_assignment_zero A Y (g3_power Y n) hdim n
      (g3_proj Y n) (fun _ => g) IT a
      (fun hi => ha (Finite.injective_iff_surjective.mp hi)) pol w
  exact s4_selected_sum_action_cupMulti A Y hdim f n R hR H (t * c ^ n) hH hz v

#print axioms s4_selected_mixed_sum_cup_action
end HodgeLean.Foundations.Program
