import HodgeLean.Foundations.Program.SchoenTransferJ12SumApplySurvivors
import HodgeLean.Foundations.Program.SchoenTransferJ12TensorActionNormalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- An assignment-annihilating tensor action evaluates actual sum pullback with its exact factorial.
Source: the actual sum survivors and the unsigned tensor-action normalization. -/
theorem s4_selected_sum_action_cupMulti
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (f : Y ⟶ A) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (R : HQ Y 1 →ₗ[ℚ] HQ A 1) (hR : R.comp (homPullback f 1) = LinearMap.id)
    (E : HQ (g3_power Y n) n →ₗ[ℚ] HQ A n) (s : ℚ)
    (hE : E.comp (s4_e1_oneCup Y n) = s •
      (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
        (PiTensorProduct.map (fun _ : Fin n => R)))
    (hzero : ∀ a : Fin n → Fin n, ¬ Function.Surjective a → ∀ w : Fin n → HQ Y 1,
      E ((cupProductOf (g3_power Y n)).cupMulti n
        (fun i => homPullback (g3_proj Y n (a i)) 1 (w i))) = 0)
    (v : Fin n → HQ A 1) :
    E (homPullback (s4_sum f n) n ((cupProductOf A).cupMulti n v)) =
      (s * (Nat.factorial n : ℚ)) • (cupProductOf A).cupMulti n v := by
  rw [s4_selected_sum_cupMulti_apply A Y f n E hzero v]
  exact s4_selected_tensor_action_unsigned_sum A Y hdim n (homPullback f 1) R hR E s hE v

#print axioms s4_selected_sum_action_cupMulti
end HodgeLean.Foundations.Program
