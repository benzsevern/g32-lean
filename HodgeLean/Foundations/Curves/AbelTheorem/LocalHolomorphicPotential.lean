import HodgeLean.Foundations.Curves.AbelTheorem.CenteredScalarAnalytic

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

/-- Source: Forster, Lectures on Riemann Surfaces, §2, local holomorphic functions. -/
theorem centered_scalar_analytic_of_eventually_mdifferentiable
    (h : Module.finrank ℂ E = 1) (G : C → ℂ) (x : C)
    (hG : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) G y) :
    AnalyticAt ℂ (centeredScalar h G x) 0 := by
  let A : ℂ → E := fun z => chartAt E x x + b4cov_lineEquiv h z
  have hA : ContinuousAt A 0 :=
    (continuous_const.add (b4cov_lineEquiv h).continuous).continuousAt
  have hA0 : A 0 = chartAt E x x := by simp [A]
  have ht : ∀ᶠ z in 𝓝 (0 : ℂ), A z ∈ (chartAt E x).target := by
    apply hA.preimage_mem_nhds
    rw [hA0]
    exact (chartAt E x).open_target.mem_nhds ((chartAt E x).map_source (mem_chart_source E x))
  have hi : ContinuousAt (fun z => (chartAt E x).symm (A z)) 0 := by
    apply ContinuousAt.comp (f := A)
      ((chartAt E x).continuousAt_symm (by rw [hA0]; exact (chartAt E x).map_source (mem_chart_source E x)))
    exact hA
  have hi0 : (chartAt E x).symm (A 0) = x := by
    rw [hA0, (chartAt E x).left_inv (mem_chart_source E x)]
  have hg : ∀ᶠ z in 𝓝 (0 : ℂ), MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) G
      ((chartAt E x).symm (A z)) := by
    have he := hi.tendsto
    rw [hi0] at he
    exact he.eventually hG
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [ht, hg] with z hz hgz
  exact centered_scalar_differentiable_of_mdifferentiable h G x z hz hgz

/-- Source: Forster, Lectures on Riemann Surfaces, §2, local holomorphic functions. -/
theorem eventually_centered_scalar_analytic_of_centered_differentiable
    (h : Module.finrank ℂ E = 1) (G : C → ℂ) (x : C)
    (hG : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (centeredScalar h G y) 0) :
    ∀ᶠ y in 𝓝 x, AnalyticAt ℂ (centeredScalar h G y) 0 := by
  have hm : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) G y := by
    filter_upwards [hG] with y hy
    exact mdifferentiable_of_centered_scalar h G y hy
  filter_upwards [eventually_eventually_nhds.mpr hm] with y hy
  exact centered_scalar_analytic_of_eventually_mdifferentiable h G y hy

end HodgeLean.Foundations.Curves.AbelTheorem
