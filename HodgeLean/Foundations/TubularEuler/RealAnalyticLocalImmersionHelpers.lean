import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Euclidean analytic immersions on the original chart neighbourhoods

The coordinate map followed by a real linear equivalence is an analytic
immersion on its actual open source in every finite dimension.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem realAnalyticEuclideanImmersion_local
    (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ω M] (x : M) :
    ∃ (n : ℕ) (f : M → EuclideanSpace ℝ (Fin n)) (U : Set M),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω f U ∧
      ∀ y ∈ U, Function.Injective
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f y) := by
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [finrank_euclideanSpace_fin]; rfl)
  have hc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ω (chartAt E x) (chartAt E x).source := by
    simpa only [mfld_simps] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := x) (n := ω))
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω L :=
    L.toContinuousLinearMap.contDiff.contMDiff
  refine ⟨n, L ∘ (chartAt E x), (chartAt E x).source,
    (chartAt E x).open_source, mem_chart_source E x,
    hL.comp_contMDiffOn hc, ?_⟩
  intro y hy
  rw [mfderiv_comp y L.differentiableAt.mdifferentiableAt
    ((mdifferentiable_chart (I := 𝓘(ℝ, E)) x).mdifferentiableAt hy), L.mfderiv_eq]
  exact L.injective.comp ((mdifferentiable_chart (I := 𝓘(ℝ, E)) x).mfderiv_injective hy)

#print axioms realAnalyticEuclideanImmersion_local

end HodgeLean.Foundations.TubularEuler
