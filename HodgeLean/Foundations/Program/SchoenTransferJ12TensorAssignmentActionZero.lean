import HodgeLean.Foundations.Program.SchoenTransferJ12CrossAssignmentActionZero
import HodgeLean.Foundations.Program.SchoenTransferJ12CrossPairPullback
import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCupMultilinear
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- General mixed tensor kernels annihilate repeated actual source assignments.
Source: multilinear extension of the repeated coordinate cross-kernel vanishing. -/
theorem s4_selected_tensor_assignment_action_zero
    (A Y T : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ) (f : Fin n → (T ⟶ Y))
    (IT : HQ T (2 * n) ≃ₗ[ℚ] ℚ) (a : Fin n → Fin n) (ha : ¬ Function.Injective a)
    (ξ : Fin n → HQ A 1 ⊗[ℚ] HQ Y 1) (u : Fin n → HQ Y 1) :
    s4_selected_corr_action A T n IT n n n (by omega)
      (s4_selected_divisor_cup (A ⊗ T) n (fun i =>
        homPullback (lift (fst A T) (snd A T ≫ f i)) 2
          (s4_selected_cross_map A Y 1 1 2 rfl (ξ i))))
      ((cupProductOf T).cupMulti n (fun i => homPullback (f (a i)) 1 (u i))) = 0 := by
  classical
  let U := HQ A 1 ⊗[ℚ] HQ Y 1
  let input := (cupProductOf T).cupMulti n (fun i => homPullback (f (a i)) 1 (u i))
  let C (i : Fin n) : U →ₗ[ℚ] HQ (A ⊗ T) 2 :=
    (homPullback (lift (fst A T) (snd A T ≫ f i)) 2).comp
      (s4_selected_cross_map A Y 1 1 2 rfl)
  let F : MultilinearMap ℚ (fun _ : Fin n => U) (HQ A n) :=
    ((LinearMap.applyₗ input).comp (s4_selected_kernel_linear_map A T n IT n n n (by omega))).compMultilinearMap
      ((s4_selected_divisor_cup_multilinear (A ⊗ T) n).compLinearMap C)
  have hspan : Submodule.span ℚ (Set.range (fun j : HQ A 1 × HQ Y 1 => j.1 ⊗ₜ[ℚ] j.2)) = ⊤ := by
    have he : Set.range (fun j : HQ A 1 × HQ Y 1 => j.1 ⊗ₜ[ℚ] j.2) =
        {t : U | ∃ a b, a ⊗ₜ[ℚ] b = t} := by
      ext t
      constructor
      · rintro ⟨⟨a, b⟩, rfl⟩
        exact ⟨a, b, rfl⟩
      · rintro ⟨a, b, rfl⟩
        exact ⟨(a, b), rfl⟩
    rw [he]
    exact TensorProduct.span_tmul_eq_top ℚ (HQ A 1) (HQ Y 1)
  have hF : F = 0 := by
    apply MultilinearMap.ext_of_span_eq_top
      (g := fun {_ : Fin n} (j : HQ A 1 × HQ Y 1) => j.1 ⊗ₜ[ℚ] j.2) (fun _ => hspan)
    intro j
    change s4_selected_corr_action A T n IT n n n _
      (s4_selected_divisor_cup_multilinear (A ⊗ T) n (fun i => C i ((j i).1 ⊗ₜ[ℚ] (j i).2))) input = 0
    rw [s4_selected_divisor_cup_multilinear_apply]
    have hC : (fun i => C i ((j i).1 ⊗ₜ[ℚ] (j i).2)) =
        (fun i => (cupProductOf (A ⊗ T)).cup rfl
          (homPullback (fst A T) 1 (j i).1)
          (homPullback (snd A T) 1 (homPullback (f i) 1 (j i).2))) := by
      funext i
      exact s4_selected_cross_pair_pullback A Y T (f i) 1 1 2 rfl (j i).1 (j i).2
    rw [hC]
    exact s4_selected_cross_assignment_action_zero A Y T hdim n f IT a ha
      (fun i => (j i).1) (fun i => (j i).2) u
  have hh := congrArg (fun H => H ξ) hF
  change s4_selected_corr_action A T n IT n n n _
    (s4_selected_divisor_cup_multilinear (A ⊗ T) n (fun i => C i (ξ i))) input = 0 at hh
  rw [s4_selected_divisor_cup_multilinear_apply] at hh
  exact hh

#print axioms s4_selected_tensor_assignment_action_zero
end HodgeLean.Foundations.Program
