import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFourBidegrees

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The bidegree formula for the degree-four fibre projection. -/
theorem s4_selected_projection_four_bidegrees
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (i k : Fin 3)
    (a : HQ A i.val) (b : HQ Y (2 - i.val))
    (c : HQ A k.val) (d : HQ Y (2 - k.val)) :
    s4_selected_projection A Y 1 2 I
      ((cupProductOf (A ⊗ Y)).cup rfl
        (s4_selected_cross_two A Y i a b) (s4_selected_cross_two A Y k c d)) =
      if h : i.val + k.val = 2 then
        ((-1 : ℚ) ^ ((2 - i.val) * k.val)) •
          (I ((cupProductOf Y).cup (by have := i.isLt; have := k.isLt; omega) b d) •
            (cupProductOf A).cup h a c)
      else 0 := by
  split_ifs with h
  · exact s4_selected_projection_four_bidegrees_pair A Y I i k h a b c d
  · exact s4_selected_projection_four_bidegrees_zero A Y I i k h a b c d

#print axioms s4_selected_projection_four_bidegrees
end HodgeLean.Foundations.Program
