import HodgeLean.Foundations.Program.SchoenTransferJ12MixedKernelCoordinates
import HodgeLean.Foundations.Program.SchoenTransferE1Defs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual mixed product kernel agrees with the tensor action on all-degree-one curve-power cups.
Source: the actual coordinate action and the universal ordered tensor product. -/
theorem s4_selected_mixed_kernel_oneCup
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (IY : HQ Y 2 ≃ₗ[ℚ] ℚ) (IT : HQ (g3_power Y n) (2 * n) ≃ₗ[ℚ] ℚ)
    (g : Y ⟶ A) (pol : HQ A 2) :
    (s4_selected_corr_action A (g3_power Y n) n IT n n n (by omega)
      (s4_selected_mixed_divisor_kernel A (g3_power Y n) n
        (fun i => g3_proj Y n i ≫ g) pol)).comp (s4_e1_oneCup Y n) =
    IT (s4_selected_divisor_cup (g3_power Y n) n
      (fun i => homPullback (g3_proj Y n i) 2 (IY.symm 1))) •
      (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
        (PiTensorProduct.map (fun _ : Fin n =>
          s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
            (s4_selected_curve_mixed_divisor A Y g pol))) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.lift.tprod, s4_e1_oneCup, MultilinearMap.compLinearMap_apply]
  change s4_selected_corr_action A (g3_power Y n) n IT n n n _ _
    ((cupProductOf (g3_power Y n)).cupMulti n
      (fun i => homPullback (g3_proj Y n i) 1 (v i))) =
    IT (s4_selected_divisor_cup (g3_power Y n) n
      (fun i => homPullback (g3_proj Y n i) 2 (IY.symm 1))) •
      ((cupProductOf A).cupMulti n (fun i =>
        s4_selected_corr_action A Y 1 IY 1 1 1 _
          (s4_selected_curve_mixed_divisor A Y g pol) (v i)))
  exact s4_selected_mixed_kernel_coordinates A Y (g3_power Y n) n (g3_proj Y n)
    (fun _ => g) IY IT pol v

#print axioms s4_selected_mixed_kernel_oneCup
end HodgeLean.Foundations.Program
