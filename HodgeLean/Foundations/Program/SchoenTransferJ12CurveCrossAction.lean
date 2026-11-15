import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionEvenCross
import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- A mixed degree-one cross kernel acts by the actual cup pairing on the fibre.
Source: Fulton, Intersection Theory, §16.1, correspondence actions;
Hatcher, Algebraic Topology, §3.2, associativity and naturality of cup. -/
theorem s4_selected_curve_cross_action
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (a : HQ A 1) (b u : HQ Y 1) :
    s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num)
      ((cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (fst A Y) 1 a) (homPullback (snd A Y) 1 b)) u =
      I ((cupProductOf Y).cup rfl b u) • a := by
  unfold s4_selected_corr_action
  simp only [LinearMap.comp_apply]
  rw [(cupProductOf (A ⊗ Y)).assoc (i := 1) (j := 1) (l := 1)
    (ij := 2) (jl := 2) (k := 3) rfl rfl rfl rfl,
    ← spec_homPullback_cup]
  exact s4_selected_projection_even_cross A Y 1 1 I a ((cupProductOf Y).cup rfl b u)

#print axioms s4_selected_curve_cross_action
end HodgeLean.Foundations.Program
