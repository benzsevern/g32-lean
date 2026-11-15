import HodgeLean.Foundations.Program.MilneTensorDefs
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_associated_matrix (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hs : B.transpose = B) : B.toQuadraticForm'.associated = B.toBilin' := by
  apply QuadraticMap.associated_left_inverse
  exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr hs).eq

theorem m1b_matrix_quadratic_coordinates (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hs : B.transpose = B) : B.toQuadraticForm'.toMatrix' = B := by
  rw [QuadraticForm.toMatrix', m1b_associated_matrix n B hs]
  exact (LinearMap.toMatrix₂' ℂ).apply_symm_apply B

theorem m1b_alternating_even (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = -B) : Even n := by
  by_contra hn
  have ho : Odd n := Nat.not_even_iff_odd.mp hn
  have hd := congrArg Matrix.det hs
  rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin, ho.neg_one_pow,
    neg_one_mul] at hd
  have hz : B.det = 0 := by
    have hh : (2 : ℂ) * B.det = 0 := by
      calc (2 : ℂ) * B.det = B.det + B.det := by ring
           _ = B.det + -B.det := congrArg (fun x => B.det + x) hd
           _ = 0 := add_neg_cancel _
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  exact (hB.map Matrix.detMonoidHom).ne_zero hz

def m1b_matrix_unit (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := LinearMap.toMatrix' e.toLinearMap
  inv := LinearMap.toMatrix' e.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_mul]
    have h : e.toLinearMap * e.symm.toLinearMap = 1 := by
      apply LinearMap.ext
      exact e.apply_symm_apply
    rw [h, LinearMap.toMatrix'_one]
  inv_val := by
    rw [← LinearMap.toMatrix'_mul]
    have h : e.symm.toLinearMap * e.toLinearMap = 1 := by
      apply LinearMap.ext
      exact e.symm_apply_apply
    rw [h, LinearMap.toMatrix'_one]

end HodgeLean.Foundations.Program
