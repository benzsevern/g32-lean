import HodgeLean.Foundations.Program.MilneTensorMatrixOrbit

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_matrix_bilin_alternating (Q : Matrix ι ι ℂ) (hQ : Q.transpose = -Q)
    (x : ι → ℂ) : Q.toBilin' x x = 0 := by
  rw [Matrix.toBilin'_apply']
  apply CharZero.eq_neg_self_iff.mp
  have h := Matrix.dotProduct_transpose_mulVec Q x x
  rw [hQ, Matrix.neg_mulVec, dotProduct_neg] at h
  exact h.symm

end HodgeLean.Foundations.Program
