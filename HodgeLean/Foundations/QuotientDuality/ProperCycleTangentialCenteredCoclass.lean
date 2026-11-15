import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialCenteredSource
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartRestriction

/-! # Literal normal coclasses under actual tangential centering
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Tangential centering retains the literal original normal coclass on each actual chart neighborhood.
Source: properCycle_tangential_centered_chart and chartNormalProjectionCoclass, whose point maps retain the original normal coordinate.
HC no distance; AV milestone no distance. -/
lemma properCycle_tangential_centered_coclass
    {M : Type} [TopologicalSpace M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ))) (v : Fin r → ℂ)
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hb : ∀ y ∈ (properCycle_tangential_centered_chart r d e v).source,
      y ∈ S ↔ ((properCycle_tangential_centered_chart r d e v) y).2 = 0)
    (W : Set M) (hW : W ⊆ e.source)
    (hWb : W ⊆ (properCycle_tangential_centered_chart r d e v).source) :
    chartNormalProjectionCoclass (Fin r → ℂ) d
      (properCycle_tangential_centered_chart r d e v) S hb W hWb =
    chartNormalProjectionCoclass (Fin r → ℂ) d e S hS W hW := rfl

end HodgeLean.Foundations.QuotientDuality
