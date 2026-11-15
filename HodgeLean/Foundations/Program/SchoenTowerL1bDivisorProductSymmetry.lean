import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductFunction
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFieldPullbackCongr
import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A permutation fixes the coordinate product in the actual generic field. -/
theorem s2v_l1b_divisor_product_function_permute
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    (σ : Equiv.Perm (Fin n)) (u : Y.left.functionField) :
    letI : IsIso (s2_permute Y n σ) := (s2_permuteIso Y n σ).isIso_hom
    s2v_l1b_functionFieldPullback (s2_permute Y n σ).left
      (s2v_l1b_divisor_product_function Y n u) =
        s2v_l1b_divisor_product_function Y n u := by
  letI : IsIso (s2_permute Y n σ) := (s2_permuteIso Y n σ).isIso_hom
  letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
    s2v_l1b_divisor_projection_dominant Y n
  unfold s2v_l1b_divisor_product_function
  rw [map_prod]
  calc
    _ = ∏ j : Fin n, s2v_l1b_functionFieldPullback (g3_proj Y n (σ.symm j)).left u := by
      apply Finset.prod_congr rfl
      intro j _
      have hj : (s2_permute Y n σ).left ≫ (g3_proj Y n j).left =
          (g3_proj Y n (σ.symm j)).left :=
        congrArg Over.Hom.left (s2_check_lift_proj n _ j)
      have H := s2v_l1b_divisor_functionFieldPullback_congr _ _ hj
      rw [s2v_l1b_functionFieldPullback_comp] at H
      exact congrArg (fun k : Y.left.functionField ⟶ (g3_power Y n).left.functionField => k u) H
    _ = _ := Equiv.prod_comp σ.symm (fun j => s2v_l1b_functionFieldPullback (g3_proj Y n j).left u)

end HodgeLean.Foundations.Program
