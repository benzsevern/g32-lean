import HodgeLean.Foundations.Matrix.Cayley

noncomputable section
namespace HodgeLean.Foundations
open MatrixCayley

/-- Negating a Cayley parameter inverts the chart matrix. -/
theorem pel_cayley_inverse {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n k) (hplus : (1 + X).det ≠ 0) :
    (cayley X)⁻¹ = cayley (-X) := by
  rw [cayley, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hplus)]
  simp only [cayley, sub_neg_eq_add, sub_eq_add_neg, neg_neg]

#print axioms pel_cayley_inverse
end HodgeLean.Foundations
