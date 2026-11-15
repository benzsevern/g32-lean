import HodgeLean.Foundations.TubularEuler.AnalyticImmersionChartBridgeHelpers

/-! # Euclidean coordinates for finite dimensional analytic immersion targets

A real continuous linear equivalence transports a finite dimensional target
to standard Euclidean coordinates while retaining all immersion derivatives.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem realAnalyticEuclideanImmersion_of_finiteDimensional_target
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ω M]
    (f : M → H) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) f x)) :
    ∃ (n : ℕ) (g : M → EuclideanSpace ℝ (Fin n)),
      (∀ z, ContDiffOn ℝ ω (fun a => g ((chartAt E z).symm a)) (chartAt E z).target) ∧
      (∀ z a, a ∈ (chartAt E z).target →
        Function.Injective (fderiv ℝ (fun b => g ((chartAt E z).symm b)) a)) := by
  let n := Module.finrank ℝ H
  let L : H ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [finrank_euclideanSpace_fin]; rfl)
  have hL : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω L :=
    L.toContinuousLinearMap.contDiff.contMDiff
  have hg := hL.comp hf
  have hgi : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (L ∘ f) x) := by
    intro x
    rw [mfderiv_comp x L.differentiableAt.mdifferentiableAt
      (hf.mdifferentiableAt (by simp)), L.mfderiv_eq]
    exact L.injective.comp (hi x)
  exact ⟨n, L ∘ f, analyticImmersion_chart_contDiffOn hg,
    analyticImmersion_chart_fderiv_injective hg hgi⟩

#print axioms realAnalyticEuclideanImmersion_of_finiteDimensional_target

end HodgeLean.Foundations.TubularEuler
