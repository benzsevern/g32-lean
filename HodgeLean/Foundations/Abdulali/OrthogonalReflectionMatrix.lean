import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Abdulali
open Matrix
variable {n : ℕ}

/-- Reflection in the hyperplane perpendicular to a nonisotropic vector,
written as a rational function of that vector.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
def orthogonalReflectionMatrix (u : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - (2 / (u ⬝ᵥ u)) • vecMulVec u u

/-- The rational reflection matrix is symmetric.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
theorem orthogonalReflectionMatrix_transpose (u : Fin n → ℂ) :
    (orthogonalReflectionMatrix u).transpose = orthogonalReflectionMatrix u := by
  simp only [orthogonalReflectionMatrix, transpose_sub, transpose_one,
    transpose_smul, transpose_vecMulVec]

/-- A reflection in a nonisotropic vector squares to the identity.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
theorem orthogonalReflectionMatrix_sq (u : Fin n → ℂ) (hu : u ⬝ᵥ u ≠ 0) :
    orthogonalReflectionMatrix u * orthogonalReflectionMatrix u = 1 := by
  have hh : vecMulVec u u * vecMulVec u u = (u ⬝ᵥ u) • vecMulVec u u := by
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
    ring
  simp only [orthogonalReflectionMatrix, mul_sub, sub_mul, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hh, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [hu]
  <;> ring

/-- Reflection matrices are isometries for the standard symmetric form.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
theorem orthogonalReflectionMatrix_isometry (u : Fin n → ℂ) (hu : u ⬝ᵥ u ≠ 0) :
    (orthogonalReflectionMatrix u).transpose * 1 * orthogonalReflectionMatrix u = 1 := by
  rw [orthogonalReflectionMatrix_transpose, mul_one, orthogonalReflectionMatrix_sq u hu]

#print axioms orthogonalReflectionMatrix_transpose
#print axioms orthogonalReflectionMatrix_sq
#print axioms orthogonalReflectionMatrix_isometry
end HodgeLean.Foundations.Abdulali
