import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace HodgeLean.Adapters

/-- Critical values of a complex differentiable map in equal dimensions have zero volume. -/
theorem a3b4a_gysin_complex_critical_values_null
    {n : ℕ} (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (f : (Fin n → ℂ) → (Fin n → ℂ)) (hf : DifferentiableOn ℂ f U) :
    MeasureTheory.volume
      (f '' {x | x ∈ U ∧ ¬ IsUnit (fderiv ℂ f x)}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ := MeasureTheory.volume)
    (f' := fun x => (fderiv ℂ f x).restrictScalars ℝ)
  · intro x hx
    exact ((hf x hx.1).differentiableAt (hU.mem_nhds hx.1)).hasFDerivAt.restrictScalars
      ℝ |>.hasFDerivWithinAt
  · intro x hx
    by_contra hdet
    have hu : IsUnit (((fderiv ℂ f x).restrictScalars ℝ).toLinearMap) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    apply hx.2
    apply ContinuousLinearMap.isUnit_iff_bijective.mpr
    exact (Module.End.isUnit_iff (((fderiv ℂ f x).restrictScalars ℝ).toLinearMap)).mp hu

/-- Arbitrarily small parameters avoid every member of a countable family of null sets. -/
theorem a3b4a_gysin_small_parameter_avoiding_null_sets
    {n : ℕ} {ι : Type*} [Countable ι]
    (S : ι → Set (Fin n → ℂ)) (hS : ∀ j, MeasureTheory.volume (S j) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Fin n → ℂ, ‖a‖ < ε ∧ ∀ j, a ∉ S j := by
  have hnull : MeasureTheory.volume (⋃ j, S j) = 0 :=
    MeasureTheory.measure_iUnion_null hS
  have hdense : Dense ((⋃ j, S j)ᶜ) :=
    MeasureTheory.Measure.dense_of_ae (μ := MeasureTheory.volume) (by
      simpa only [MeasureTheory.ae_iff, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq] using hnull)
  obtain ⟨a, ha, hball⟩ := hdense.exists_mem_open Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hε⟩
  refine ⟨a, ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right] using hball
  · intro j hj
    exact ha (Set.mem_iUnion.mpr ⟨j, hj⟩)

end HodgeLean.Adapters
