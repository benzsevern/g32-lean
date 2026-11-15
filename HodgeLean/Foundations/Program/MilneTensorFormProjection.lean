import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*}

def m1b_matrixFormProjection (ε : ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun Q := (2 : ℂ)⁻¹ • (Q + ε • Q.transpose)
  map_add' Q R := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  map_smul' c Q := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      RingHom.id_apply, smul_eq_mul]
    ring

theorem m1b_matrixFormProjection_transpose (ε : ℂ) (hε : ε ^ 2 = 1)
    (Q : Matrix ι ι ℂ) :
    (m1b_matrixFormProjection ε Q).transpose = ε • m1b_matrixFormProjection ε Q := by
  ext i j
  change (2 : ℂ)⁻¹ * (Q j i + ε * Q i j) =
    ε * ((2 : ℂ)⁻¹ * (Q i j + ε * Q j i))
  ring_nf
  rw [hε]
  ring

theorem m1b_matrixFormProjection_fixed (ε : ℂ) (hε : ε ^ 2 = 1)
    (Q : Matrix ι ι ℂ) (hQ : Q.transpose = ε • Q) :
    m1b_matrixFormProjection ε Q = Q := by
  ext i j
  have h := congrArg (fun A : Matrix ι ι ℂ => A i j) hQ
  change Q j i = ε * Q i j at h
  change (2 : ℂ)⁻¹ * (Q i j + ε * Q j i) = Q i j
  rw [h]
  ring_nf
  rw [hε]
  ring

theorem m1b_matrixFormProjection_congruence [Fintype ι] (ε : ℂ)
    (M Q : Matrix ι ι ℂ) :
    m1b_matrixFormProjection ε (M.transpose * Q * M) =
      M.transpose * m1b_matrixFormProjection ε Q * M := by
  change (2 : ℂ)⁻¹ • (M.transpose * Q * M + ε • (M.transpose * Q * M).transpose) =
    M.transpose * ((2 : ℂ)⁻¹ • (Q + ε • Q.transpose)) * M
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, smul_add]

end HodgeLean.Foundations.Program
