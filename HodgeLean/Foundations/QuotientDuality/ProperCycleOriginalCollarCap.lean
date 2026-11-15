import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalSupportCollar

/-! # Original cycle support cap on its retained actual collar
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The retained actual collar has exactly the original middle support cap, with its original scalar and supported and homology groups.
Source: properCycle_original_support_cap; properCycle_projective_support_cap.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_collar_cap
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) :
    (properCycle_original_support_collar X γ).cap (a3b4a_classSupport_isClosed X.hom γ)
      (2*k) (2*k) c = properCycle_original_support_cap X γ k c := rfl

end HodgeLean.Foundations.QuotientDuality
