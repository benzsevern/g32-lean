import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceCross
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionBaseOffDegree

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- An external correspondence summand vanishes when its base degree differs from the output degree.
Source: cup associativity and the specified off-degree fibre trace calculation. -/
theorem s4_selected_corr_action_cross_off_degree
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (c r t u v : ℕ) (h : 2 * c + r = 2 * d + t)
    (huv : u + v = 2 * c) (hut : u ≠ t)
    (a : HQ A u) (b : HQ Y v) (x : HQ Y r) :
    s4_selected_corr_action A Y d I c r t h
      ((cupProductOf (A ⊗ Y)).cup huv
        (homPullback (fst A Y) u a) (homPullback (snd A Y) v b)) x = 0 := by
  unfold s4_selected_corr_action
  simp only [LinearMap.comp_apply]
  rw [(cupProductOf (A ⊗ Y)).assoc huv rfl h (by omega),
    ← spec_homPullback_cup (snd A Y) rfl]
  exact s4_selected_projection_base_off_degree A Y d t u (v + r) (by omega) I (by omega) a _

#print axioms s4_selected_corr_action_cross_off_degree
end HodgeLean.Foundations.Program
