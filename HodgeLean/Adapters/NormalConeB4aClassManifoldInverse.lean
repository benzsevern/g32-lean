import HodgeLean.Adapters.NormalConeB4aClassAnalyticInverseFinite
import HodgeLean.Adapters.NormalConeB4aClassChartRegularity

/-! # Inverse regularity for charts on complex manifolds

Route: compose with a manifold chart at the inverse image point. The resulting
map is an analytic local homeomorphism of finite-dimensional complex spaces.
Apply analytic inverse regularity and return through the manifold chart.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open scoped Manifold ContDiff

/-- A complex analytic chart on a finite-dimensional complex manifold has an
analytic manifold inverse on its target. -/
theorem a3b4a_classManifoldChart_inverse
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    (e : OpenPartialHomeomorph M F)
    (he : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) ω e e.source) :
    ContMDiffOn 𝓘(ℂ, F) 𝓘(ℂ, E) ω e.symm e.target := by
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  let x := e.symm y
  let l := chartAt E x
  have hx : x ∈ l.source := mem_chart_source E x
  let t := l.symm.trans e
  have ht : AnalyticOnNhd ℂ t t.source := by
    intro z hz
    have hL : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω l.symm z :=
      (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (n := ω) (x := x)).contMDiffAt
        (l.open_target.mem_nhds hz.1)
    have hE : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ω e (l.symm z) :=
      (he _ hz.2).contMDiffAt (e.open_source.mem_nhds hz.2)
    exact (hE.comp z hL).contDiffAt.analyticAt
  have hyt : y ∈ t.target := ⟨hy, hx⟩
  have hi : AnalyticAt ℂ t.symm y := a3b4a_classAnalyticInverse_finiteDimensional t ht y hyt
  have hL : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω l.symm (t.symm y) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (n := ω) (x := x)).contMDiffAt
      (l.open_target.mem_nhds (l.map_source hx))
  apply (hL.comp y hi.contDiffAt.contMDiffAt).congr_of_eventuallyEq
  have hlocal : ∀ᶠ w in 𝓝 y, e.symm w ∈ l.source :=
    (e.continuousAt_symm hy).eventually (l.open_source.mem_nhds hx)
  filter_upwards [hlocal] with w hw
  exact (l.left_inv hw).symm

end HodgeLean.Adapters
