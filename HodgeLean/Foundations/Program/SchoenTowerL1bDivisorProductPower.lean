import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductFunction
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFieldPullbackCongr

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Coordinate products commute with powers of rational functions. -/
theorem s2v_l1b_divisor_product_function_pow
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    (u : Y.left.functionField) (m : ℕ) :
    s2v_l1b_divisor_product_function Y n u ^ m =
      s2v_l1b_divisor_product_function Y n (u ^ m) := by
  unfold s2v_l1b_divisor_product_function
  rw [← Finset.prod_pow]
  simp only [map_pow]

/-- Coordinate products commute with generic pullback along the coordinatewise map. -/
theorem s2v_l1b_divisor_product_function_pullback
    (Y Z : Over (Spec ↧ℂ)) [IsIntegral Y.left] [IsIntegral Z.left]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (f : Y ⟶ Z) [IsDominant f.left] (n : ℕ)
    [IsIntegral (g3_power Y n).left] [IsIntegral (g3_power Z n).left]
    [IsDominant (s2_powerMap f n).left] (v : Z.left.functionField) :
    s2v_l1b_divisor_product_function Y n (s2v_l1b_functionFieldPullback f.left v) =
      s2v_l1b_functionFieldPullback (s2_powerMap f n).left
        (s2v_l1b_divisor_product_function Z n v) := by
  letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
    s2v_l1b_divisor_projection_dominant Y n
  letI : ∀ j : Fin n, IsDominant (g3_proj Z n j).left :=
    s2v_l1b_divisor_projection_dominant Z n
  unfold s2v_l1b_divisor_product_function
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  have hj : (s2_powerMap f n).left ≫ (g3_proj Z n j).left =
      (g3_proj Y n j).left ≫ f.left :=
    congrArg Over.Hom.left (s2_check_lift_proj n _ j)
  have H := congrArg (fun k : Z.left.functionField ⟶ (g3_power Y n).left.functionField => k v)
    (show s2v_l1b_functionFieldPullback ((s2_powerMap f n).left ≫ (g3_proj Z n j).left) =
      s2v_l1b_functionFieldPullback ((g3_proj Y n j).left ≫ f.left) by
        exact s2v_l1b_divisor_functionFieldPullback_congr _ _ hj)
  rw [s2v_l1b_functionFieldPullback_comp, s2v_l1b_functionFieldPullback_comp] at H
  exact H.symm

end HodgeLean.Foundations.Program
