import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Field.Rat

/-! # Linear extension from a rational generator -/

noncomputable section
namespace HodgeLean.Foundations.QuotientDuality

lemma properCycle_linear_extension_unique
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (a : V) (b : W)
    (ha : Function.Bijective (LinearMap.toSpanSingleton ℚ V a)) :
    ∃! F : V →ₗ[ℚ] W, F a = b := by
  let e : ℚ ≃ₗ[ℚ] V := LinearEquiv.ofBijective _ ha
  let F : V →ₗ[ℚ] W := (LinearMap.toSpanSingleton ℚ W b).comp e.symm.toLinearMap
  have he : e 1 = a := one_smul ℚ a
  have hFa : F a = b := by
    change e.symm a • b = b
    rw [← he, e.symm_apply_apply, one_smul]
  refine ⟨F, hFa, ?_⟩
  intro G hG
  ext v
  obtain ⟨q, hq⟩ := ha.2 v
  rw [← hq]
  change G (q • a) = F (q • a)
  rw [map_smul, map_smul, hG, hFa]

end HodgeLean.Foundations.QuotientDuality
