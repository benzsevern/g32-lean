import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalSupportCap

/-! # The actual collar retained by the original cycle support cap
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Retain the actual selected projective collar used by the original cycle support cap, on the literal analytic cycle support.
Source: properCycle_projective_support_collar; a3b4a_classAlgebraicSupport.
HC no distance; AV milestone no distance. -/
def properCycle_original_support_collar
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ) :
    ProperCycleSupportCollar (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ) :=
  properCycle_projective_support_collar X (a3b4a_classAlgebraicSupport X.hom γ)

example (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (z : a3b4_an X.hom) (hz : z ∈ a3b4_cycleSupport X.hom γ) :
    z ∈ (properCycle_original_support_collar X γ).neighborhood :=
  (properCycle_original_support_collar X γ).contains hz

end HodgeLean.Foundations.QuotientDuality
