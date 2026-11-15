import HodgeLean.Foundations.Program.SchoenTransferJ12CrossCupAction
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveCoordinatePairing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Pure coordinate cross kernels act by the product of the curve contractions without a residual sign.
Source: cancellation of the two actual ordered cup permutation signs. -/
theorem s4_selected_coordinate_cross_action
    (A Y T : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (n : ℕ) (f : Fin n → (T ⟶ Y))
    (IY : HQ Y 2 ≃ₗ[ℚ] ℚ) (IT : HQ T (2 * n) ≃ₗ[ℚ] ℚ)
    (a : Fin n → HQ A 1) (b u : Fin n → HQ Y 1) :
    s4_selected_corr_action A T n IT n n n (by omega)
      (s4_selected_divisor_cup (A ⊗ T) n (fun i =>
        (cupProductOf (A ⊗ T)).cup rfl
          (homPullback (fst A T) 1 (a i))
          (homPullback (snd A T) 1 (homPullback (f i) 1 (b i)))))
      ((cupProductOf T).cupMulti n (fun i => homPullback (f i) 1 (u i))) =
    ((∏ i, IY ((cupProductOf Y).cup rfl (b i) (u i))) *
      IT (s4_selected_divisor_cup T n (fun i => homPullback (f i) 2 (IY.symm 1)))) •
        ((cupProductOf A).cupMulti n a) := by
  rw [s4_selected_cross_cup_action]
  have hp := s4_selected_curve_coordinate_pairing Y T n f IY IT.toLinearMap b u
  change IT _ = _ at hp
  simp only [LinearEquiv.coe_coe] at hp
  rw [hp]
  have hs : ((-1 : ℚ) ^ n.choose 2) * ((-1 : ℚ) ^ n.choose 2) = 1 := by
    rw [← mul_pow]
    norm_num
  apply congrArg (fun c : ℚ => c • ((cupProductOf A).cupMulti n a))
  calc
    _ = (((-1 : ℚ) ^ n.choose 2) * ((-1 : ℚ) ^ n.choose 2)) *
        ((∏ i, IY ((cupProductOf Y).cup rfl (b i) (u i))) *
          IT (s4_selected_divisor_cup T n (fun i => homPullback (f i) 2 (IY.symm 1)))) := by ring
    _ = _ := by rw [hs, one_mul]

#print axioms s4_selected_coordinate_cross_action
end HodgeLean.Foundations.Program
