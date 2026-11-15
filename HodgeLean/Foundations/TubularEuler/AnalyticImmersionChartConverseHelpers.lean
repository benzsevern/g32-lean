import HodgeLean.Foundations.TubularEuler.AnalyticImmersionChartBridgeHelpers

/-! # Tangent injectivity from the original analytic chart derivatives

The chart calculation is independent of the scheme carrying the manifold.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 30000
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- Faithful derivatives in the original charts give a faithful manifold derivative.
Source: Lee, Introduction to Smooth Manifolds, second edition, chapter 3,
coordinate description of the tangent map.
HC no distance; AV milestone no distance. -/
theorem analyticImmersion_mfderiv_injective_of_chart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ω M]
    (f : M → H) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ω f)
    (hi : ∀ z a, a ∈ (chartAt E z).target → Function.Injective
      (fderiv ℝ (fun b => f ((chartAt E z).symm b)) a)) (x : M) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) f x) := by
  let a := (chartAt E x) x
  have ha : a ∈ (chartAt E x).target :=
    (chartAt E x).map_source (mem_chart_source _ x)
  let g := fun b => f ((chartAt E x).symm b)
  have hgi : Function.Injective (fderiv ℝ g a) := hi x a ha
  have hmi : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) g a) := by
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (g a)).symm.injective.comp
      (hgi.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) a).injective)
  have hfx := hf.mdifferentiableAt (x := (chartAt E x).symm a) (by simp)
  change Function.Injective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (f ∘ (chartAt E x).symm) a) at hmi
  rw [mfderiv_comp a hfx
    ((mdifferentiable_chart (I := 𝓘(ℝ, E)) x).symm.mdifferentiableAt ha)] at hmi
  have hs := (mdifferentiable_chart (I := 𝓘(ℝ, E)) x).symm.mfderiv_surjective ha
  have hback : Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) f ((chartAt E x).symm a)) :=
    Function.Injective.of_comp_right hmi hs
  have hxi : (chartAt E x).symm a = x := (chartAt E x).left_inv (mem_chart_source _ x)
  exact Eq.mp (congrArg (fun y : M =>
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) f y)) hxi) hback

example (x : ℝ) : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
    (fun t : ℝ => 2 * t) x) := by
  apply analyticImmersion_mfderiv_injective_of_chart _
    ((contDiff_const.mul contDiff_id).contMDiff)
  intro z a ha
  simp only [mfld_simps, id_eq]
  have he : fderiv ℝ (fun t : ℝ => 2 * t) a =
      (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    simpa using ((hasFDerivAt_id a).const_mul (2 : ℝ)).fderiv
  rw [he]
  intro u v h
  change 2 * u = 2 * v at h
  linarith

#print axioms analyticImmersion_mfderiv_injective_of_chart
end HodgeLean.Foundations.TubularEuler
