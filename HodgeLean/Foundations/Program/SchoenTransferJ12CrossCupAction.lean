import HodgeLean.Foundations.Program.SchoenTransferJ12CrossCupProduct
import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceCross
import HodgeLean.Foundations.Program.SchoenTransferJ12KernelLinearMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- An ordered product of pure mixed crosses acts by the signed top fibre pairing.
Source: the external cup permutation sign and the matching correspondence action. -/
theorem s4_selected_cross_cup_action
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) (I : HQ Y (2 * n) ≃ₗ[ℚ] ℚ)
    (a : Fin n → HQ A 1) (b : Fin n → HQ Y 1) (x : HQ Y n) :
    s4_selected_corr_action A Y n I n n n (by omega)
      (s4_selected_divisor_cup (A ⊗ Y) n (fun i =>
        (cupProductOf (A ⊗ Y)).cup rfl
          (homPullback (fst A Y) 1 (a i)) (homPullback (snd A Y) 1 (b i)))) x =
    (((-1 : ℚ) ^ n.choose 2) *
      I ((cupProductOf Y).cup (by omega : n + n = 2 * n)
        ((cupProductOf Y).cupMulti n b) x)) • ((cupProductOf A).cupMulti n a) := by
  rw [s4_selected_cross_cup_product]
  have hs := LinearMap.congr_fun
    ((s4_selected_kernel_linear_map A Y n I n n n (by omega)).map_smul
      ((-1 : ℚ) ^ n.choose 2)
      ((cupProductOf (A ⊗ Y)).cup (by omega : n + n = 2 * n)
        (homPullback (fst A Y) n ((cupProductOf A).cupMulti n a))
        (homPullback (snd A Y) n ((cupProductOf Y).cupMulti n b)))) x
  change s4_selected_corr_action A Y n I n n n _ _ x =
    ((-1 : ℚ) ^ n.choose 2) • s4_selected_corr_action A Y n I n n n _ _ x at hs
  rw [hs, s4_selected_corr_action_cross, smul_smul]

#print axioms s4_selected_cross_cup_action
end HodgeLean.Foundations.Program
