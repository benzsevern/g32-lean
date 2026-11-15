import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedAction
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedContraction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The degree-one endomorphism obtained from a divisor by its actual mixed curve kernel. -/
def s4_selected_curve_divisor_operator
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) : HQ A 2 →ₗ[ℚ] Module.End ℚ (HQ A 1) :=
  ((s4_selected_kernel_linear_map A Y 1 I 1 1 1 (by norm_num)).comp
    (s4_selected_curve_mixed_linear A Y f)).compl₂ (homPullback f 1)

/-- A decomposable divisor acts by the two contractions against the pulled curve pairing. -/
theorem s4_selected_curve_divisor_operator_cup
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (v w z : HQ A 1) :
    s4_selected_curve_divisor_operator A Y f I ((cupProductOf A).cup rfl v w) z =
      I ((cupProductOf Y).cup rfl (homPullback f 1 w) (homPullback f 1 z)) • v -
        I ((cupProductOf Y).cup rfl (homPullback f 1 v) (homPullback f 1 z)) • w := by
  exact s4_selected_curve_mixed_divisor_action A Y f I v w (homPullback f 1 z)

#print axioms s4_selected_curve_divisor_operator
#print axioms s4_selected_curve_divisor_operator_cup
end HodgeLean.Foundations.Program
