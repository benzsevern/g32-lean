import HodgeLean.Foundations.Program.SchoenTransferJ12CurveAddBidegrees
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveJordanLinear

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- On decomposable inputs the actual fibre-integral Jordan operation has four contraction terms. -/
theorem s4_selected_curve_jordan_cups
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (v w s t : HQ A 1) :
    s4_selected_curve_jordan A Y f I
      ((cupProductOf A).cup rfl v w) ((cupProductOf A).cup rfl s t) =
    (2 : ℚ)⁻¹ •
      (-I ((cupProductOf Y).cup rfl (homPullback f 1 w) (homPullback f 1 t)) •
          (cupProductOf A).cup rfl v s +
        I ((cupProductOf Y).cup rfl (homPullback f 1 w) (homPullback f 1 s)) •
          (cupProductOf A).cup rfl v t +
        I ((cupProductOf Y).cup rfl (homPullback f 1 v) (homPullback f 1 t)) •
          (cupProductOf A).cup rfl w s -
        I ((cupProductOf Y).cup rfl (homPullback f 1 v) (homPullback f 1 s)) •
          (cupProductOf A).cup rfl w t) := by
  have hfour : (-1 : ℚ) ^ 4 = 1 := by norm_num
  unfold s4_selected_curve_jordan
  rw [spec_homPullback_cup (s4_selected_curve_add_map A Y f),
    s4_selected_curve_add_cup_bidegrees, s4_selected_curve_add_cup_bidegrees]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    s4_selected_projection_four_bidegrees]
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, ↓reduceDIte]
  simp only [show (4 : ℕ) ≠ 2 from by decide, show (3 : ℕ) ≠ 2 from by decide,
    show (1 : ℕ) ≠ 2 from by decide, show (0 : ℕ) ≠ 2 from by decide, dite_false]
  simp only [hfour, pow_zero, pow_one, CupProduct.one_cup, CupProduct.cup_one,
    one_smul, neg_one_smul, spec_homPullback_cup, zero_smul, sub_zero, zero_add, add_zero]
  module

#print axioms s4_selected_curve_jordan_cups
end HodgeLean.Foundations.Program
