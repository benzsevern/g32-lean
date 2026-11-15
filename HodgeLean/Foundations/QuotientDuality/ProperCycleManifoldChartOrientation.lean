import HodgeLean.Adapters.NormalConeB4aClassManifoldInverse
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothHolomorphicChart
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

/-! # Actual orientation comparison for complex analytic manifold charts -/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicTopology.Singular HodgeLean.Adapters
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.QuotientDuality

/-- The original transition between two analytic charts on a complex manifold is analytic on its literal source.
Source: a3b4a_classManifoldChart_inverse; ContMDiffAt.comp.
HC no distance; AV milestone no distance. -/
theorem properCycle_manifold_chart_transition_analytic
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    {d : ℕ} (e e' : OpenPartialHomeomorph M (Fin d → ℂ))
    (he : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin d → ℂ) ω e e.source)
    (he' : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin d → ℂ) ω e' e'.source) :
    AnalyticOnNhd ℂ (e.symm.trans e') (e.symm.trans e').source := by
  have hei := a3b4a_classManifoldChart_inverse e he
  intro z hz
  have h₁ := (hei z hz.1).contMDiffAt (e.open_target.mem_nhds hz.1)
  have h₂ := (he' (e.symm z) hz.2).contMDiffAt (e'.open_source.mem_nhds hz.2)
  exact (h₂.comp z h₁).contDiffAt.analyticAt

/-- The original normalized local classes agree in any two analytic charts on a complex manifold.
Source: properCycle_manifold_chart_transition_analytic; localClassOfChart_eq_of_analyticAt_transition.
HC no distance; AV milestone no distance. -/
theorem properCycle_manifold_chart_local_class_eq
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    {d : ℕ} (e e' : OpenPartialHomeomorph M (Fin d → ℂ))
    (he : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin d → ℂ) ω e e.source)
    (he' : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin d → ℂ) ω e' e'.source)
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    localClassOfChart d e x hx = localClassOfChart d e' x hx' := by
  apply localClassOfChart_eq_of_analyticAt_transition
  · apply properCycle_manifold_chart_transition_analytic e e' he he' (e x)
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rw [e.left_inv hx]
    exact hx'
  · apply properCycle_manifold_chart_transition_analytic e' e he' he (e' x)
    refine ⟨e'.map_source hx', ?_⟩
    change e'.symm (e' x) ∈ e.source
    rw [e'.left_inv hx']
    exact hx

end HodgeLean.Foundations.QuotientDuality
