import HodgeLean.Adapters.NormalConeB4aClassAnalyticInverse
import HodgeLean.Adapters.NormalConeB4aClassChartDimension

/-! # Analytic inverse regularity without a dimension hypothesis

Route: a nonempty chart has equal dimensions by the regular-germ argument.
The equal-dimensional inverse theorem then applies. Empty chart targets
require no pointwise verification.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Topology

/-- An analytic local homeomorphism between arbitrary finite complex
coordinate spaces has an analytic inverse on its target. -/
theorem a3b4a_classAnalyticInverse_dimensions
    {n m : ℕ} (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin m → ℂ))
    (ha : AnalyticOnNhd ℂ e e.source) : AnalyticOnNhd ℂ e.symm e.target := by
  by_cases hne : e.source.Nonempty
  · have hdim := a3b4a_classAnalyticChart_dimensions e ha hne
    subst m
    exact a3b4a_classAnalyticInverse e ha
  · intro y hy
    exact (hne ⟨e.symm y, e.map_target hy⟩).elim

end HodgeLean.Adapters
