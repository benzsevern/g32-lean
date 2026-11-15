import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialCenteredSource
import HodgeLean.Foundations.QuotientDuality.ProperCycleHolomorphicSubConst

/-! # Original holomorphic coordinates under actual tangential translations
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Translating only the original tangential coordinates preserves the original holomorphic chart predicate.
Source: properCycle_holomorphic_sub_const; anb_isHolFun_restrict; a3b4_IsHolChart.
HC no distance; AV milestone no distance. -/
lemma properCycle_tangential_centered_chart_holomorphic
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (r d : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (v : Fin r → ℂ) :
    a3b4_IsHolChart X.hom (properCycle_tangential_centered_chart r d e v) := by
  let c := properCycle_tangential_centered_chart r d e v
  have hsub : c.source ⊆ e.source := fun _ h => h.1
  constructor
  · intro j
    have h := anb_isHolFun_restrict (f4_analytification X).atlas hsub (he.1 j)
    exact properCycle_holomorphic_sub_const (f4_analytification X) c.source _ h (v j)
  · intro j
    exact anb_isHolFun_restrict (f4_analytification X).atlas hsub (he.2 j)

end HodgeLean.Foundations.QuotientDuality
