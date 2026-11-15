import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Real.Basic

/-! Unit leading coefficients permit monic normalization without changing any real root fiber. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_monic_normalization {R : Type*} [CommRing R]
    (p : Polynomial R) (hp : IsUnit p.leadingCoeff) :
    ∃ q : Polynomial R, q.Monic ∧
      ∀ (φ : R →+* ℝ) (t : ℝ), p.eval₂ φ t = 0 ↔ q.eval₂ φ t = 0 := by
  let q := hp.unit⁻¹ • p
  refine ⟨q, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hp, ?_⟩
  intro φ t
  have hφ : φ (↑(hp.unit⁻¹) : R) ≠ 0 := (hp.unit⁻¹).isUnit.map φ |>.ne_zero
  change p.eval₂ φ t = 0 ↔ (hp.unit⁻¹ • p).eval₂ φ t = 0
  rw [Units.smul_def, Polynomial.smul_eq_C_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  exact (mul_eq_zero_iff_left hφ).symm

end HodgeLean.Foundations.Program
