import HodgeLean.Foundations.Abdulali.OrthogonalReflectionMatrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Abdulali
open Matrix
variable {n : ℕ}

/-- A reflection in a nonisotropic complex vector has determinant minus one.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
theorem orthogonalReflectionMatrix_det (u : Fin n → ℂ) (hu : u ⬝ᵥ u ≠ 0) :
    (orthogonalReflectionMatrix u).det = -1 := by
  have he : orthogonalReflectionMatrix u =
      1 + replicateCol Unit ((-2 / (u ⬝ᵥ u)) • u) * replicateRow Unit u := by
    ext i j
    simp [orthogonalReflectionMatrix, Matrix.mul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp
  <;> ring

/-- The reflection as an actual invertible matrix, with its inverse retained.
Source: Weyl, The Classical Groups, Chapter II, §9, orthogonal reflections. -/
def orthogonalReflectionGL (u : Fin n → ℂ) (hu : u ⬝ᵥ u ≠ 0) :
    Matrix.GeneralLinearGroup (Fin n) ℂ :=
  ⟨orthogonalReflectionMatrix u, orthogonalReflectionMatrix u,
    orthogonalReflectionMatrix_sq u hu, orthogonalReflectionMatrix_sq u hu⟩

#print axioms orthogonalReflectionMatrix_det
end HodgeLean.Foundations.Abdulali
