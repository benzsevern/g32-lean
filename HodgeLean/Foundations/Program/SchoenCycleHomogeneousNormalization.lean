import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions

/-! # Normalization of analytic homogeneous coordinates -/
noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A nonzero analytic homogeneous lift has an analytic reciprocal coordinate for normalization.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15. -/
theorem s2e_analytic_homogeneous_coordinate_normalization
    {n d : ℕ} (a : (Fin d → ℂ) → (Fin n → ℂ))
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0)
    (L : (Fin n → ℂ) →ₗ[ℂ] ℂ) :
    ∃ (i : Fin n) (η : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, η z * a z i = 1) ∧
      (∀ z, L (fun j => η z * a z j) = η z * L (a z)) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a 0 i ≠ 0 := by
    by_contra! h
    apply ha0
    exact funext h
  have hai : AnalyticAt ℂ (fun z => a z i) 0 :=
    ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt (a 0)).comp ha
  refine ⟨i, (fun z => (a z i)⁻¹), hai.inv hi, inv_ne_zero hi, ?_, ?_⟩
  · filter_upwards [hai.continuousAt.eventually_ne hi] with z hz
    exact inv_mul_cancel₀ hz
  · intro z
    exact L.map_smul ((a z i)⁻¹) (a z)

end HodgeLean.Foundations.Program
