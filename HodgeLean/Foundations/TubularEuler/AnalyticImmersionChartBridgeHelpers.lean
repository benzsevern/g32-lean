import HodgeLean.Foundations.TubularEuler.RealAnalyticLocalImmersionHelpers
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Original chart coefficients of an analytic manifold immersion

An analytic map and its injective tangent derivative give analytic coordinate
maps and injective ordinary derivatives in every original chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ω M]

theorem analyticImmersion_chart_contDiffOn {f : M → H}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ω f) (z : M) :
    ContDiffOn ℝ ω (fun a => f ((chartAt E z).symm a)) (chartAt E z).target := by
  have h := hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) z)
  simpa only [contMDiffOn_iff_contDiffOn, mfld_simps, Function.comp_def] using h

theorem analyticImmersion_chart_fderiv_injective {f : M → H}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) f x))
    (z : M) (a : E) (ha : a ∈ (chartAt E z).target) :
    Function.Injective (fderiv ℝ (fun b => f ((chartAt E z).symm b)) a) := by
  let g : E → H := fun b => f ((chartAt E z).symm b)
  have hcomp : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) g a) := by
    change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (f ∘ (chartAt E z).symm) a)
    rw [mfderiv_comp a (hf.mdifferentiableAt (by simp))
      ((mdifferentiable_chart (I := 𝓘(ℝ, E)) z).symm.mdifferentiableAt ha)]
    exact (hi _).comp ((mdifferentiable_chart (I := 𝓘(ℝ, E)) z).symm.mfderiv_injective ha)
  let A := NormedSpace.fromTangentSpace (𝕜 := ℝ) a
  intro u w huw
  have he : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) g a (A.symm u) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) g a (A.symm w) := by
    rw [mfderiv_eq_fderiv]
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (g a)).symm
        (fderiv ℝ g a (A (A.symm u))) =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (g a)).symm
        (fderiv ℝ g a (A (A.symm w)))
    rw [A.apply_symm_apply, A.apply_symm_apply]
    exact congrArg _ huw
  exact A.symm.injective (hcomp he)

#print axioms analyticImmersion_chart_fderiv_injective

#print axioms analyticImmersion_chart_contDiffOn

end HodgeLean.Foundations.TubularEuler
