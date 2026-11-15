import HodgeLean.Foundations.Program.SchoenTransferJ12CurveCrossAction

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

/-- A matching external correspondence kernel acts by its actual fibre cup pairing.
Source: the actual fibre contraction on external top cups and cup associativity. -/
theorem s4_selected_corr_action_cross
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (c r t v : ℕ) (h : 2 * c + r = 2 * d + t) (hv : t + v = 2 * c)
    (a : HQ A t) (b : HQ Y v) (x : HQ Y r) :
    s4_selected_corr_action A Y d I c r t h
      ((cupProductOf (A ⊗ Y)).cup hv
        (homPullback (fst A Y) t a) (homPullback (snd A Y) v b)) x =
      I ((cupProductOf Y).cup (by omega : v + r = 2 * d) b x) • a := by
  unfold s4_selected_corr_action
  simp only [LinearMap.comp_apply]
  rw [(cupProductOf (A ⊗ Y)).assoc hv (by omega : v + r = 2 * d) h (by omega),
    ← spec_homPullback_cup (snd A Y) (by omega : v + r = 2 * d)]
  exact s4_selected_projection_even_cross A Y d t I a _

#print axioms s4_selected_corr_action_cross
end HodgeLean.Foundations.Program
