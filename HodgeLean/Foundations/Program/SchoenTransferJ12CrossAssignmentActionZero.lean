import HodgeLean.Foundations.Program.SchoenTransferJ12CurveAssignmentPairZero
import HodgeLean.Foundations.Program.SchoenTransferJ12CrossCupAction

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

/-- Pure coordinate cross kernels annihilate every repeated input assignment.
Source: the repeated curve-coordinate pairing and the actual cross kernel action formula. -/
theorem s4_selected_cross_assignment_action_zero
    (A Y T : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ) (f : Fin n → (T ⟶ Y))
    (I : HQ T (2 * n) ≃ₗ[ℚ] ℚ) (a : Fin n → Fin n) (ha : ¬ Function.Injective a)
    (w : Fin n → HQ A 1) (b v : Fin n → HQ Y 1) :
    s4_selected_corr_action A T n I n n n (by omega)
      (s4_selected_divisor_cup (A ⊗ T) n (fun i =>
        (cupProductOf (A ⊗ T)).cup rfl (homPullback (fst A T) 1 (w i))
          (homPullback (snd A T) 1 (homPullback (f i) 1 (b i)))))
      ((cupProductOf T).cupMulti n (fun i => homPullback (f (a i)) 1 (v i))) = 0 := by
  have hp := s4_selected_curve_assignment_pair_zero Y T hdim n f a ha b v
  have hz := congrArg (HQ.castEquiv T (by omega : n + n = 2 * n)) hp
  rw [CupProduct.castEquiv_cup, map_zero] at hz
  rw [s4_selected_cross_cup_action, hz, map_zero, mul_zero, zero_smul]

#print axioms s4_selected_cross_assignment_action_zero
end HodgeLean.Foundations.Program
