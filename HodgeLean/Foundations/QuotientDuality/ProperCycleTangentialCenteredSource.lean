import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialCenteredChart

/-! # Literal source and normal coordinate of translated product charts
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual tangential translation keeps the original chart source and retains its original normal coordinate.
Source: properCycle_tangential_centered_chart; OpenPartialHomeomorph.trans.
HC no distance; AV milestone no distance. -/
lemma properCycle_tangential_centered_chart_data
    {M : Type} [TopologicalSpace M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ))) (v : Fin r → ℂ) :
    (properCycle_tangential_centered_chart r d e v).source = e.source ∧
      ∀ x, properCycle_tangential_centered_chart r d e v x = ((e x).1 - v, (e x).2) := by
  constructor
  · change e.source ∩ e ⁻¹' Set.univ = e.source
    rw [Set.preimage_univ, Set.inter_univ]
  · intro x
    rfl

end HodgeLean.Foundations.QuotientDuality
