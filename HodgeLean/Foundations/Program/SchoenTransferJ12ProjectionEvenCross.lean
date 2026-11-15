import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionCross

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Integration of a base-first external cup has no sign for an even-dimensional fibre class.
Source: Hatcher, Algebraic Topology, §3.2, graded commutativity of external cups. -/
theorem s4_selected_projection_even_cross
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (a : HQ A n) (b : HQ Y (2 * d)) :
    s4_selected_projection A Y d n I
      ((cupProductOf (A ⊗ Y)).cup (Nat.add_comm n (2 * d))
        (homPullback (fst A Y) n a) (homPullback (snd A Y) (2 * d) b)) = I b • a := by
  have hs : (-1 : ℚ) ^ ((2 * d) * n) = 1 := by
    rw [show (2 * d) * n = 2 * (d * n) by ring, pow_mul]
    norm_num
  have hc := (cupProductOf (A ⊗ Y)).graded_comm rfl (Nat.add_comm n (2 * d))
    (homPullback (snd A Y) (2 * d) b) (homPullback (fst A Y) n a)
  rw [hs, one_smul] at hc
  rw [hc]
  exact s4_selected_projection_fibre_cross A Y d n I b a

#print axioms s4_selected_projection_even_cross
end HodgeLean.Foundations.Program
