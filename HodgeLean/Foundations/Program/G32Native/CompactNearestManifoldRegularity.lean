import HodgeLean.Foundations.Program.G32Native.CompactNearestModelTransport
import HodgeLean.Foundations.TubularEuler.AnalyticImmersionChartBridgeHelpers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Analyticity of the actual compact nearest-point retraction

The manifold chart expression is transported through a finite-dimensional
Hilbert model. The resulting map is still the one compact nearest selection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Function Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- The common nearest-base selection of an analytically immersed compact
carrier is analytic at every image point from the carrier's interior.
Source: `compactNearest_chart_analytic_of_model_equiv`,
`analyticImmersion_chart_contDiffOn`, and
`analyticImmersion_chart_fderiv_injective`.
HC no distance; AV milestone no distance. -/
theorem compactNearest_retraction_analyticAt
    {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ω M]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (C : Set M) [CompactSpace C] [Nonempty C]
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ω e)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x))
    (hemb : Topology.IsEmbedding (fun z : C => e z)) (c : C)
    (hcC : (c : M) ∈ interior C) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ω
      (fun y => ((CompactNearest.nearest (fun z : C => e z)
        (he.continuous.comp continuous_subtype_val) y : C) : M)) (e c) := by
  let B := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : B ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq
    (by simp only [B, finrank_euclideanSpace_fin])
  let r : F → M := fun y => ((CompactNearest.nearest (fun z : C => e z)
    (he.continuous.comp continuous_subtype_val) y : C) : M)
  have hr0 : r (e c) = c := congrArg Subtype.val
    (CompactNearest.nearest_fix (fun z : C => e z)
      (he.continuous.comp continuous_subtype_val) hemb.injective c)
  have hrt : Filter.Tendsto r (𝓝 (e c)) (𝓝 (c : M)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      (CompactNearest.nearest_tendsto (fun z : C => e z)
        (he.continuous.comp continuous_subtype_val) hemb c)
  have hcont : ContinuousAt r (e c) := by
    change Filter.Tendsto r (𝓝 (e c)) (𝓝 (r (e c)))
    rw [hr0]
    exact hrt
  let a := chartAt E (c : M)
  have hc : (c : M) ∈ a.source := mem_chart_source E _
  have htarget : a c ∈ a.target := a.map_source hc
  have hσ : ContDiffAt ℝ ⊤ (fun b => e (a.symm b)) (a c) :=
    (analyticImmersion_chart_contDiffOn he c).contDiffAt (a.open_target.mem_nhds htarget)
  have hinj := analyticImmersion_chart_fderiv_injective he hi c (a c) htarget
  have hchart := compactNearest_chart_analytic_of_model_equiv L C e he.continuous
    hemb a c hc hcC hσ hinj
  change ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ω r (e c)
  apply contMDiffAt_iff_target.mpr
  refine ⟨hcont, ?_⟩
  simpa only [hr0, mfld_simps, contMDiffAt_iff_contDiffAt, Function.comp_def] using hchart

#print axioms compactNearest_retraction_analyticAt

end HodgeLean.Foundations.TubularEuler
