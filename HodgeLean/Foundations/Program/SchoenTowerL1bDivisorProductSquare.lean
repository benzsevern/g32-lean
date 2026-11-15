import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductPower

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained quotient square transports the product binomial to its descended functions. -/
theorem s2v_l1b_divisor_product_descended_power
    (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsIntegral Z.left] [IsIntegral W.left] [IsIntegral B.left]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (f : Y ⟶ Z) [IsDominant f.left] (n : ℕ)
    [IsIntegral (g3_power Y n).left] [IsIntegral (g3_power Z n).left]
    [IsDominant (s2_powerMap f n).left]
    (q : g3_power Y n ⟶ W) [IsDominant q.left]
    (γ : g3_power Z n ⟶ B) [IsDominant γ.left]
    (β : W ⟶ B) [IsDominant β.left]
    (hsquare : q ≫ β = s2_powerMap f n ≫ γ)
    (u : Y.left.functionField) (v : Z.left.functionField) (m : ℕ)
    (hpow : u ^ m = s2v_l1b_functionFieldPullback f.left v)
    (w : W.left.functionField) (b : B.left.functionField)
    (hw : s2v_l1b_functionFieldPullback q.left w = s2v_l1b_divisor_product_function Y n u)
    (hb : s2v_l1b_functionFieldPullback γ.left b = s2v_l1b_divisor_product_function Z n v) :
    w ^ m = s2v_l1b_functionFieldPullback β.left b := by
  apply (s2v_l1b_functionFieldPullback q.left).hom.injective
  rw [map_pow, hw, s2v_l1b_divisor_product_function_pow, hpow,
    s2v_l1b_divisor_product_function_pullback, ← hb]
  have H := s2v_l1b_divisor_functionFieldPullback_congr
    (q.left ≫ β.left) ((s2_powerMap f n).left ≫ γ.left)
    (congrArg Over.Hom.left hsquare)
  rw [s2v_l1b_functionFieldPullback_comp, s2v_l1b_functionFieldPullback_comp] at H
  exact (congrArg (fun k : B.left.functionField ⟶ (g3_power Y n).left.functionField => k b) H).symm

end HodgeLean.Foundations.Program
