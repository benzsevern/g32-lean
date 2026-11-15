import HodgeLean.Foundations.Program.SchoenTransferJ12CoordinateCrossAction
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

/-- Actual coordinate products of general mixed tensors act factor by factor on coordinate cups.
Source: the pure coordinate action and multilinear extension from the tensor generators. -/
theorem s4_selected_tensor_kernel_coordinates
    (A Y T : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (n : ℕ) (f : Fin n → (T ⟶ Y))
    (IY : HQ Y 2 ≃ₗ[ℚ] ℚ) (IT : HQ T (2 * n) ≃ₗ[ℚ] ℚ)
    (ξ : Fin n → HQ A 1 ⊗[ℚ] HQ Y 1) (u : Fin n → HQ Y 1) :
    s4_selected_corr_action A T n IT n n n (by omega)
      (s4_selected_divisor_cup (A ⊗ T) n (fun i =>
        homPullback (lift (fst A T) (snd A T ≫ f i)) 2
          (s4_selected_cross_map A Y 1 1 2 rfl (ξ i))))
      ((cupProductOf T).cupMulti n (fun i => homPullback (f i) 1 (u i))) =
    IT (s4_selected_divisor_cup T n (fun i => homPullback (f i) 2 (IY.symm 1))) •
      ((cupProductOf A).cupMulti n (fun i =>
        s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
          (s4_selected_cross_map A Y 1 1 2 rfl (ξ i)) (u i))) := by
  classical
  let U := HQ A 1 ⊗[ℚ] HQ Y 1
  let input := (cupProductOf T).cupMulti n (fun i => homPullback (f i) 1 (u i))
  let topScalar := IT (s4_selected_divisor_cup T n (fun i => homPullback (f i) 2 (IY.symm 1)))
  let C (i : Fin n) : U →ₗ[ℚ] HQ (A ⊗ T) 2 :=
    (homPullback (lift (fst A T) (snd A T ≫ f i)) 2).comp
      (s4_selected_cross_map A Y 1 1 2 rfl)
  let R (i : Fin n) : U →ₗ[ℚ] HQ A 1 :=
    (LinearMap.applyₗ (u i)).comp
      ((s4_selected_kernel_linear_map A Y 1 IY 1 1 1 (by omega)).comp
        (s4_selected_cross_map A Y 1 1 2 rfl))
  let F : MultilinearMap ℚ (fun _ : Fin n => U) (HQ A n) :=
    ((LinearMap.applyₗ input).comp (s4_selected_kernel_linear_map A T n IT n n n (by omega))).compMultilinearMap ((s4_selected_divisor_cup_multilinear (A ⊗ T) n).compLinearMap C)
  let G : MultilinearMap ℚ (fun _ : Fin n => U) (HQ A n) :=
    topScalar • ((cupProductOf A).cupMulti n).compLinearMap R
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
  have hFG : F = G := by
    apply MultilinearMap.ext_of_span_eq_top
      (g := fun {_ : Fin n} (j : HQ A 1 × HQ Y 1) => j.1 ⊗ₜ[ℚ] j.2) (fun _ => hspan)
    intro j
    change s4_selected_corr_action A T n IT n n n _
      (s4_selected_divisor_cup_multilinear (A ⊗ T) n (fun i => C i ((j i).1 ⊗ₜ[ℚ] (j i).2))) input = _
    rw [s4_selected_divisor_cup_multilinear_apply]
    have hC : (fun i => C i ((j i).1 ⊗ₜ[ℚ] (j i).2)) =
        (fun i => (cupProductOf (A ⊗ T)).cup rfl
          (homPullback (fst A T) 1 (j i).1)
          (homPullback (snd A T) 1 (homPullback (f i) 1 (j i).2))) := by
      funext i
      exact s4_selected_cross_pair_pullback A Y T (f i) 1 1 2 rfl (j i).1 (j i).2
    rw [hC]
    rw [s4_selected_coordinate_cross_action]
    change _ = topScalar • ((cupProductOf A).cupMulti n (fun i => R i ((j i).1 ⊗ₜ[ℚ] (j i).2)))
    have hR (i : Fin n) : R i ((j i).1 ⊗ₜ[ℚ] (j i).2) =
        IY ((cupProductOf Y).cup rfl (j i).2 (u i)) • (j i).1 := by
      exact s4_selected_curve_cross_action A Y IY (j i).1 (j i).2 (u i)
    simp only [hR]
    rw [MultilinearMap.map_smul_univ, smul_smul]
    exact congrArg (fun c : ℚ => c • ((cupProductOf A).cupMulti n (fun i => (j i).1)))
      (mul_comm _ topScalar)
  have hh := congrArg (fun H => H ξ) hFG
  change s4_selected_corr_action A T n IT n n n _
    (s4_selected_divisor_cup_multilinear (A ⊗ T) n (fun i => C i (ξ i))) input = _ at hh
  rw [s4_selected_divisor_cup_multilinear_apply] at hh
  exact hh

#print axioms s4_selected_tensor_kernel_coordinates
end HodgeLean.Foundations.Program
