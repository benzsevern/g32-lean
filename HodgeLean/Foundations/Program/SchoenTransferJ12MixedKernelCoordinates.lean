import HodgeLean.Foundations.Program.SchoenTransferJ12TensorKernelCoordinates
import HodgeLean.Foundations.Program.SchoenTransferJ12MixedDivisorNaturality
import HodgeLean.Foundations.Program.SchoenTransferJ12MixedDivisorBidegree
import HodgeLean.Foundations.Program.SchoenTransferJ12MixedKernelCurveCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual mixed divisor product acts factor by factor on actual coordinate degree-one cups.
Source: the actual mixed bidegree tensors, their pair pullbacks and the coordinate action formula. -/
theorem s4_selected_mixed_kernel_coordinates
    (A Y T : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (n : ℕ) (f : Fin n → (T ⟶ Y)) (g : Fin n → (Y ⟶ A))
    (IY : HQ Y 2 ≃ₗ[ℚ] ℚ) (IT : HQ T (2 * n) ≃ₗ[ℚ] ℚ)
    (pol : HQ A 2) (u : Fin n → HQ Y 1) :
    s4_selected_corr_action A T n IT n n n (by omega)
      (s4_selected_mixed_divisor_kernel A T n (fun i => f i ≫ g i) pol)
      ((cupProductOf T).cupMulti n (fun i => homPullback (f i) 1 (u i))) =
    IT (s4_selected_divisor_cup T n (fun i => homPullback (f i) 2 (IY.symm 1))) •
      ((cupProductOf A).cupMulti n (fun i =>
        s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
          (s4_selected_curve_mixed_divisor A Y (g i) pol) (u i))) := by
  have hex (i : Fin n) : ∃ ξ : HQ A 1 ⊗[ℚ] HQ Y 1,
      s4_selected_cross_map A Y 1 1 2 rfl ξ =
        s4_selected_curve_mixed_divisor A Y (g i) pol :=
    s4_selected_mixed_divisor_bidegree A Y (g i) pol
  choose ξ hξ using hex
  have h := s4_selected_tensor_kernel_coordinates A Y T n f IY IT ξ u
  have hD (i : Fin n) :
      homPullback (lift (fst A T) (snd A T ≫ f i)) 2
        (s4_selected_cross_map A Y 1 1 2 rfl (ξ i)) =
      s4_selected_curve_mixed_divisor A T (f i ≫ g i) pol := by
    rw [hξ i, s4_selected_mixed_divisor_naturality]
  rw [s4_selected_mixed_kernel_curve_cup]
  simp only [hD] at h
  simpa only [hξ] using h

#print axioms s4_selected_mixed_kernel_coordinates
end HodgeLean.Foundations.Program
