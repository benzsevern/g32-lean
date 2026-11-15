import HodgeLean.Foundations.Program.MilneTensorFormOrbit
import Mathlib.LinearAlgebra.Matrix.SchurComplement

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def m1b_upperBlockUnit (X : Matrix m n R) : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ where
  val := Matrix.fromBlocks 1 X 0 1
  inv := Matrix.fromBlocks 1 (-X) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

theorem m1b_symmetric_unit_inverse (A : (Matrix m m R)ˣ) (hA : A.val.transpose = A.val) :
    A.inv.transpose = A.inv := by
  have ht := congrArg Matrix.transpose A.val_inv
  rw [Matrix.transpose_mul, hA, Matrix.transpose_one] at ht
  calc
    A.inv.transpose = A.inv.transpose * (A.val * A.inv) := by
      rw [A.val_inv, mul_one]
    _ = (A.inv.transpose * A.val) * A.inv := (mul_assoc _ _ _).symm
    _ = A.inv := by rw [ht, one_mul]

theorem m1b_skew_unit_inverse (A : (Matrix m m R)ˣ) (hA : A.val.transpose = -A.val) :
    A.inv.transpose = -A.inv := by
  have ht := congrArg Matrix.transpose A.val_inv
  rw [Matrix.transpose_mul, hA, Matrix.mul_neg, Matrix.transpose_one] at ht
  have hh : A.inv.transpose * A.val = -1 := neg_eq_iff_eq_neg.mp ht
  calc
    A.inv.transpose = A.inv.transpose * (A.val * A.inv) := by rw [A.val_inv, mul_one]
    _ = (A.inv.transpose * A.val) * A.inv := (mul_assoc _ _ _).symm
    _ = -A.inv := by rw [hh, neg_one_mul]

theorem m1b_block_congruence (A : (Matrix m m R)ˣ) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R)
    (h : (A.inv * B).transpose = C * A.inv) :
    (m1b_upperBlockUnit (-(A.inv * B))).val.transpose * Matrix.fromBlocks A.val B C D *
      (m1b_upperBlockUnit (-(A.inv * B))).val =
      Matrix.fromBlocks A.val 0 0 (D - C * A.inv * B) := by
  have hAB : A.val * (A.inv * B) = B := by
    rw [← Matrix.mul_assoc, A.val_inv, Matrix.one_mul]
  change (Matrix.fromBlocks 1 (-(A.inv * B)) 0 1).transpose *
    Matrix.fromBlocks A.val B C D * Matrix.fromBlocks 1 (-(A.inv * B)) 0 1 = _
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.transpose_neg, h]
  simp only [Matrix.transpose_one, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, neg_zero, add_zero, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.mul_assoc, A.inv_val, hAB,
    add_neg_cancel, sub_eq_add_neg, add_comm]

theorem m1b_symmetric_schur_congruence (A : (Matrix m m R)ˣ)
    (hA : A.val.transpose = A.val) (B : Matrix m n R) (D : Matrix n n R) :
    (m1b_upperBlockUnit (-(A.inv * B))).val.transpose *
      Matrix.fromBlocks A.val B B.transpose D * (m1b_upperBlockUnit (-(A.inv * B))).val =
      Matrix.fromBlocks A.val 0 0 (D - B.transpose * A.inv * B) := by
  apply m1b_block_congruence
  rw [Matrix.transpose_mul, m1b_symmetric_unit_inverse A hA]

theorem m1b_alternating_schur_congruence (A : (Matrix m m R)ˣ)
    (hA : A.val.transpose = -A.val) (B : Matrix m n R) (D : Matrix n n R) :
    (m1b_upperBlockUnit (-(A.inv * B))).val.transpose *
      Matrix.fromBlocks A.val B (-B.transpose) D * (m1b_upperBlockUnit (-(A.inv * B))).val =
      Matrix.fromBlocks A.val 0 0 (D + B.transpose * A.inv * B) := by
  have h : (A.inv * B).transpose = (-B.transpose) * A.inv := by
    rw [Matrix.transpose_mul, m1b_skew_unit_inverse A hA, Matrix.mul_neg, Matrix.neg_mul]
  simpa only [Matrix.neg_mul, sub_neg_eq_add] using
    m1b_block_congruence A B (-B.transpose) D h

omit [Fintype n] [DecidableEq n] in
theorem m1b_schur_symmetric (A : (Matrix m m R)ˣ) (hA : A.val.transpose = A.val)
    (B : Matrix m n R) (D : Matrix n n R) (hD : D.transpose = D) :
    (D - B.transpose * A.inv * B).transpose = D - B.transpose * A.inv * B := by
  simp only [Matrix.transpose_sub, hD, Matrix.transpose_mul, Matrix.transpose_transpose,
    m1b_symmetric_unit_inverse A hA, Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] in
theorem m1b_schur_alternating (A : (Matrix m m R)ˣ) (hA : A.val.transpose = -A.val)
    (B : Matrix m n R) (D : Matrix n n R) (hD : D.transpose = -D) :
    (D + B.transpose * A.inv * B).transpose = -(D + B.transpose * A.inv * B) := by
  simp only [Matrix.transpose_add, hD, Matrix.transpose_mul, Matrix.transpose_transpose,
    m1b_skew_unit_inverse A hA, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_add]

theorem m1b_schur_unit_iff (A : (Matrix m m R)ˣ) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) :
    IsUnit (Matrix.fromBlocks A.val B C D) ↔ IsUnit (D - C * A.inv * B) := by
  let : Invertible A.val :=
    { invOf := A.inv
      invOf_mul_self := A.inv_val
      mul_invOf_self := A.val_inv }
  exact Matrix.isUnit_fromBlocks_iff_of_invertible₁₁

end HodgeLean.Foundations.Program
