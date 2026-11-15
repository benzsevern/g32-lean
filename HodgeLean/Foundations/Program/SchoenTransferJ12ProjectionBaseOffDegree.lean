import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionOffDegree

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The base-first external cup also vanishes when its fibre degree differs from the trace degree.
Source: graded commutativity and the finite-fibre Künneth coordinate projection. -/
theorem s4_selected_projection_base_off_degree
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n r q : ℕ) (h : r + q = 2 * d + n)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (hq : q ≠ 2 * d)
    (a : HQ A r) (b : HQ Y q) :
    s4_selected_projection A Y d n I
      ((cupProductOf (A ⊗ Y)).cup h
        (homPullback (fst A Y) r a) (homPullback (snd A Y) q b)) = 0 := by
  rw [(cupProductOf (A ⊗ Y)).graded_comm (i := q) (j := r) (by omega) h
    (homPullback (snd A Y) q b) (homPullback (fst A Y) r a), map_smul,
    s4_selected_projection_off_degree A Y d n q r (by omega) I hq b a, smul_zero]

#print axioms s4_selected_projection_base_off_degree
end HodgeLean.Foundations.Program
