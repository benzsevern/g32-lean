import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- Reduced norm in the specified definite quaternion presentation. -/
def typeIIIQuaternionNorm (b : ℚ) (q : ℍ[ℚ, -3, 0, b]) : ℚ :=
  q.re ^ 2 + 3 * q.imI ^ 2 - b * q.imJ ^ 2 - 3 * b * q.imK ^ 2

/-- Quaternion multiplication by conjugation gives the reduced norm. -/
theorem typeIIIQuaternion_mul_star (b : ℚ) (q : ℍ[ℚ, -3, 0, b]) :
    q * star q = algebraMap ℚ _ (typeIIIQuaternionNorm b q) := by
  rcases q with ⟨r, i, j, k⟩
  ext <;> simp [typeIIIQuaternionNorm, QuaternionAlgebra.mk_mul_mk,
    Star.star, QuaternionAlgebra.instStarQuaternionAlgebra,
    QuaternionAlgebra.algebraMap_eq] <;> ring

/-- The reduced norm of a definite quaternion vanishes only at zero. -/
theorem typeIIIQuaternionNorm_eq_zero (b : ℚ) (hb : b < 0)
    (q : ℍ[ℚ, -3, 0, b]) : typeIIIQuaternionNorm b q = 0 ↔ q = 0 := by
  constructor
  · intro h
    have hj : 0 ≤ -b * q.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hk : 0 ≤ -(3 * b) * q.imK ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hr : q.re = 0 := by
      dsimp [typeIIIQuaternionNorm] at h
      nlinarith [sq_nonneg q.re, sq_nonneg q.imI]
    have hi : q.imI = 0 := by
      dsimp [typeIIIQuaternionNorm] at h
      nlinarith [sq_nonneg q.re, sq_nonneg q.imI]
    have hj0 : q.imJ ^ 2 = 0 := by
      have : -b * q.imJ ^ 2 = 0 := by
        dsimp [typeIIIQuaternionNorm] at h
        nlinarith [sq_nonneg q.re, sq_nonneg q.imI]
      exact (mul_eq_zero.mp this).resolve_left (by linarith)
    have hk0 : q.imK ^ 2 = 0 := by
      have : -(3 * b) * q.imK ^ 2 = 0 := by
        dsimp [typeIIIQuaternionNorm] at h
        nlinarith [sq_nonneg q.re, sq_nonneg q.imI]
      exact (mul_eq_zero.mp this).resolve_left (by linarith)
    have hjz : q.imJ = 0 := by nlinarith
    have hkz : q.imK = 0 := by nlinarith
    ext <;> simp [hr, hi, hjz, hkz]
  · rintro rfl
    simp [typeIIIQuaternionNorm]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternion_mul_star
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionNorm_eq_zero
