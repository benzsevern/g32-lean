import HodgeLean.Adapters.NormalConeB4aClassAnalyticInverseDimensions

/-! # Analytic inverse regularity in finite-dimensional complex spaces

Route: conjugate the chart by the canonical complex linear coordinate
isomorphisms, apply inverse regularity on coordinate spaces, and conjugate
back. This includes the tangent-normal product spaces of cycle charts.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open HodgeLean.Foundations.Analytic

/-- Analytic local homeomorphisms between finite-dimensional complex normed
spaces have analytic inverses on their targets. -/
theorem a3b4a_classAnalyticInverse_finiteDimensional
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (e : OpenPartialHomeomorph E F) (ha : AnalyticOnNhd ℂ e e.source) :
    AnalyticOnNhd ℂ e.symm e.target := by
  let a := (an_coord E).toHomeomorph.toOpenPartialHomeomorph
  let b := (an_coord F).toHomeomorph.toOpenPartialHomeomorph
  let η := a.symm.trans (e.trans b)
  have hη : AnalyticOnNhd ℂ η η.source := by
    intro z hz
    change AnalyticAt ℂ (fun v => an_coord F (e ((an_coord E).symm v))) z
    exact ((an_coord F).analyticAt _).comp
      ((ha _ hz.2.1).comp ((an_coord E).symm.analyticAt z))
  have hi := a3b4a_classAnalyticInverse_dimensions η hη
  intro y hy
  have hyt : an_coord F y ∈ η.target := by
    refine ⟨⟨mem_univ _, ?_⟩, mem_univ _⟩
    change (an_coord F).symm (an_coord F y) ∈ e.target
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy
  have hv (w : F) : (an_coord E).symm (η.symm (an_coord F w)) = e.symm w := by
    change (an_coord E).symm (an_coord E (e.symm ((an_coord F).symm (an_coord F w)))) = e.symm w
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  have h := ((an_coord E).symm.analyticAt _).comp
    ((hi (an_coord F y) hyt).comp ((an_coord F).analyticAt y))
  exact h.congr (Eventually.of_forall hv)

end HodgeLean.Adapters
