import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFour
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionEvenCross
import HodgeLean.Foundations.Program.SchoenTransferPairing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Multiplication of two mixed degree-one cross classes contributes one Koszul sign. -/
theorem s4_selected_projection_four_mixed_product
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (a c : HQ A 1) (b d : HQ Y 1) :
    s4_selected_projection A Y 1 2 I
      ((cupProductOf (A ⊗ Y)).cup rfl
        ((cupProductOf (A ⊗ Y)).cup rfl
          (homPullback (fst A Y) 1 a) (homPullback (snd A Y) 1 b))
        ((cupProductOf (A ⊗ Y)).cup rfl
          (homPullback (fst A Y) 1 c) (homPullback (snd A Y) 1 d))) =
      -(I ((cupProductOf Y).cup rfl b d) • (cupProductOf A).cup rfl a c) := by
  rw [s4_cup_middle_exchange (A ⊗ Y) (cupProductOf (A ⊗ Y))
    1 1 1 1 2 2 2 2 4 rfl rfl rfl rfl rfl]
  simp only [Nat.mul_one, pow_one, neg_one_smul, map_neg]
  rw [← spec_homPullback_cup, ← spec_homPullback_cup,
    s4_selected_projection_even_cross A Y 1 2 I]

#print axioms s4_selected_projection_four_mixed_product
end HodgeLean.Foundations.Program
