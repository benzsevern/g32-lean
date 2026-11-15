import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Span.Defs

/-! Rescaling a linear comparison with a specified submodule. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s4_scaled_submodule_comparison
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (K : Submodule ℚ W) (E : V ≃ₗ[ℚ] K) (f : V →ₗ[ℚ] W)
    (c : ℚ) (hc : c ≠ 0) (hf : ∀ v, f v = c • (E v : W)) :
    Function.Injective f ∧ LinearMap.range f = K := by
  constructor
  · intro v w h
    apply E.injective
    apply Subtype.ext
    rw [hf, hf] at h
    have hh := congrArg (fun w : W => c⁻¹ • w) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh
  · have heq : f = c • (K.subtype.comp E.toLinearMap) := by
      ext v
      exact hf v
    rw [heq, LinearMap.range_smul _ _ hc,
      LinearMap.range_comp_of_range_eq_top _ E.range, Submodule.range_subtype]

theorem s4_scaled_comparison_intertwine
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (E f : V →ₗ[ℚ] W) (c : ℚ) (hf : ∀ v, f v = c • E v)
    (T : Module.End ℚ W) (R : Module.End ℚ V)
    (hE : ∀ v, T (E v) = E (R v)) (v : V) :
    T (f v) = f (R v) := by
  rw [hf, map_smul, hE, hf]

end HodgeLean.Foundations.Program
