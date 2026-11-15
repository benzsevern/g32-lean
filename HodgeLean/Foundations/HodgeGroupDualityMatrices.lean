import HodgeLean.Foundations.HodgeGroupDuality
import Mathlib.LinearAlgebra.Matrix.Dual

/-! Matrix identities for the dual polarization and the two eigenspace determinants. -/

noncomputable section
namespace HodgeLean.Foundations
variable {n : ℕ}

/-- Transposition transports centralizers, reversing the displayed commutation equation. -/
theorem g2_transpose_commutes_iff (g r : Matrix (Fin n) (Fin n) ℂ) :
    g.transpose * r.transpose = r.transpose * g.transpose ↔ g * r = r * g := by
  constructor <;> intro h
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      congrArg Matrix.transpose h.symm
  · simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose h.symm

/-- The inverse Gram matrix is preserved by the transposed action. -/
theorem g2_transpose_isometry (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (Ω : Matrix (Fin n) (Fin n) ℂ) (hΩ : IsUnit Ω.det)
    (hg : (↑g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω * (g : Matrix (Fin n) (Fin n) ℂ) = Ω) :
    (↑g : Matrix (Fin n) (Fin n) ℂ) * Ω⁻¹ *
      (↑g : Matrix (Fin n) (Fin n) ℂ).transpose = Ω⁻¹ := by
  have hgi : (↑g : Matrix (Fin n) (Fin n) ℂ) * Ω⁻¹ *
      (↑g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω = 1 := by
    calc
      _ = (↑g : Matrix (Fin n) (Fin n) ℂ) * Ω⁻¹ *
          ((↑g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω * (g : Matrix (Fin n) (Fin n) ℂ)) * (↑(g⁻¹) : Matrix (Fin n) (Fin n) ℂ) := by
            simp only [Matrix.mul_assoc, Units.val_mul, Units.mul_inv, Units.val_one,
              Matrix.mul_one]
      _ = 1 := by rw [hg]; simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul Ω hΩ,
        Matrix.one_mul, Units.val_mul, Units.mul_inv, Units.val_one]
  have h := congrArg (fun M => M * Ω⁻¹) hgi
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv Ω hΩ, Matrix.mul_one,
    Matrix.one_mul] using h

/-- The two polarization isometry equations correspond under transpose. -/
theorem g2_transpose_isometry_iff (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (Ω : Matrix (Fin n) (Fin n) ℂ) (hΩ : IsUnit Ω.det) :
    (↑g : Matrix (Fin n) (Fin n) ℂ) * Ω⁻¹ *
        (↑g : Matrix (Fin n) (Fin n) ℂ).transpose = Ω⁻¹ ↔
      (↑g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω * (g : Matrix (Fin n) (Fin n) ℂ) = Ω := by
  constructor
  · intro h
    have ht := g2_transpose_isometry (g2_dualTranspose g) Ω⁻¹
      (Matrix.isUnit_nonsing_inv_det Ω hΩ) (by simpa only [g2_dualTranspose,
        Matrix.transpose_transpose] using h)
    simpa only [g2_dualTranspose, Matrix.nonsing_inv_nonsing_inv Ω hΩ, Matrix.transpose_transpose] using ht
  · exact g2_transpose_isometry g Ω hΩ

/-- Transposition preserves each eigenspace determinant in dual coordinates. -/
theorem g2_transpose_eigenDet (g P : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : g * P = P * g) :
    (g.transpose * P.transpose + (1 - P.transpose)).det = (g * P + (1 - P)).det := by
  rw [← g2_transpose_commutes_iff] at hcomm
  rw [hcomm, ← Matrix.transpose_mul, ← Matrix.transpose_one,
    ← Matrix.transpose_sub, ← Matrix.transpose_add, Matrix.det_transpose]
  rw [Matrix.transpose_one]

/-- Both determinant-one conditions survive transposition, without interchanging eigenvalues. -/
theorem g2_transpose_eigenDets_iff (g P : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : g * P = P * g) :
    ((g.transpose * P.transpose + (1 - P.transpose)).det = 1 ∧
      (g.transpose * (1 - P.transpose) + P.transpose).det = 1) ↔
    ((g * P + (1 - P)).det = 1 ∧ (g * (1 - P) + P).det = 1) := by
  have hc : g * (1 - P) = (1 - P) * g := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hcomm]
  have hsecond := g2_transpose_eigenDet g (1 - P) hc
  simp only [Matrix.transpose_sub, Matrix.transpose_one, sub_sub_cancel] at hsecond
  rw [g2_transpose_eigenDet g P hcomm, hsecond]

end HodgeLean.Foundations
