import HodgeLean.Foundations.Program.SchoenTransferJ12Projection

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual target-first correspondence action, including odd input and output cohomology degrees.
Source: Fulton, Intersection Theory, §§16.1 and 19.1. -/
def s4_selected_corr_action
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (c r t : ℕ)
    (h : 2 * c + r = 2 * d + t) (ξ : HQ (A ⊗ Y) (2 * c)) :
    HQ Y r →ₗ[ℚ] HQ A t :=
  (s4_selected_projection A Y d t I).comp
    (((cupProductOf (A ⊗ Y)).cup h ξ).comp (homPullback (snd A Y) r))

/-- The specified correspondence action is additive in its actual cohomological kernel.
Source: Fulton, Intersection Theory, §16.1, additivity of correspondence actions. -/
theorem s4_selected_corr_action_add
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (c r t : ℕ)
    (h : 2 * c + r = 2 * d + t)
    (ξ η : HQ (A ⊗ Y) (2 * c)) :
    s4_selected_corr_action A Y d I c r t h (ξ + η) =
      s4_selected_corr_action A Y d I c r t h ξ +
        s4_selected_corr_action A Y d I c r t h η := by
  ext x
  simp only [s4_selected_corr_action, LinearMap.comp_apply, map_add,
    LinearMap.add_apply]

#print axioms s4_selected_corr_action_add

end HodgeLean.Foundations.Program
