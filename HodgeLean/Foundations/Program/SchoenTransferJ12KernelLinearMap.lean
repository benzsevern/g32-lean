import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual graded correspondence action is a linear map in its kernel.
Source: Fulton, Intersection Theory, §16.1, rational linearity of correspondence actions. -/
def s4_selected_kernel_linear_map
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (c r t : ℕ)
    (h : 2 * c + r = 2 * d + t) :
    HQ (A ⊗ Y) (2 * c) →ₗ[ℚ] (HQ Y r →ₗ[ℚ] HQ A t) where
  toFun := s4_selected_corr_action A Y d I c r t h
  map_add' := s4_selected_corr_action_add A Y d I c r t h
  map_smul' a ξ := by
    ext x
    simp only [s4_selected_corr_action, LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

#print axioms s4_selected_kernel_linear_map
end HodgeLean.Foundations.Program
