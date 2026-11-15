import HodgeLean.Adapters.NormalConeB4aClassAnalyticInverseFinite

/-! # Dimension equality for finite-dimensional analytic chart domains

Route: conjugate by complex linear coordinates and apply dimension equality
for nonempty analytic local homeomorphisms of coordinate spaces.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Topology
open HodgeLean.Foundations.Analytic

/-- A nonempty analytic local homeomorphism between finite-dimensional complex
normed spaces preserves complex dimension. -/
theorem a3b4a_classAnalyticChart_finrank
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (e : OpenPartialHomeomorph E F) (ha : AnalyticOnNhd ℂ e e.source)
    (hne : e.source.Nonempty) : Module.finrank ℂ E = Module.finrank ℂ F := by
  let a := (an_coord E).toHomeomorph.toOpenPartialHomeomorph
  let b := (an_coord F).toHomeomorph.toOpenPartialHomeomorph
  let η := a.symm.trans (e.trans b)
  have hη : AnalyticOnNhd ℂ η η.source := by
    intro z hz
    change AnalyticAt ℂ (fun v => an_coord F (e ((an_coord E).symm v))) z
    exact ((an_coord F).analyticAt _).comp
      ((ha _ hz.2.1).comp ((an_coord E).symm.analyticAt z))
  obtain ⟨x, hx⟩ := hne
  have hsource : an_coord E x ∈ η.source := by
    refine ⟨mem_univ _, ?_, mem_univ _⟩
    change (an_coord E).symm (an_coord E x) ∈ e.source
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  exact a3b4a_classAnalyticChart_dimensions η hη ⟨_, hsource⟩

end HodgeLean.Adapters
