import HodgeLean.Foundations.Abdulali.OrthogonalReflectionAction

noncomputable section
set_option maxHeartbeats 200000
open Matrix
namespace HodgeLean.Foundations.Abdulali

/-- Extend a matrix by the identity on a distinguished first coordinate. -/
def orthogonalTailMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j =>
  Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => M i j) j) i

@[simp] theorem orthogonalTailMatrix_zero_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    orthogonalTailMatrix M 0 0 = 1 := rfl
@[simp] theorem orthogonalTailMatrix_zero_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    orthogonalTailMatrix M 0 j.succ = 0 := rfl
@[simp] theorem orthogonalTailMatrix_succ_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    orthogonalTailMatrix M i.succ 0 = 0 := rfl
@[simp] theorem orthogonalTailMatrix_succ_succ {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : orthogonalTailMatrix M i.succ j.succ = M i j := rfl

/-- The distinguished-coordinate extension respects matrix multiplication. -/
def orthogonalTailMatrixHom (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (n+1)) (Fin (n+1)) ℂ where
  toFun := orthogonalTailMatrix
  map_one' := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [orthogonalTailMatrix, Matrix.one_apply, Fin.succ_ne_zero, eq_comm]
  map_mul' A B := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [orthogonalTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The same extension on invertible matrices. -/
def orthogonalTailGL (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) ℂ →*
    Matrix.GeneralLinearGroup (Fin (n+1)) ℂ := Units.map (orthogonalTailMatrixHom n)

/-- A reflection in the tail coordinates extends to the reflection in the
same vector with zero distinguished coordinate. -/
theorem orthogonalTailMatrix_reflection {n : ℕ} (v : Fin n → ℂ) :
    orthogonalTailMatrix (orthogonalReflectionMatrix v) =
      orthogonalReflectionMatrix (Fin.cons 0 v) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [orthogonalTailMatrix, orthogonalReflectionMatrix, Matrix.one_apply,
      vecMulVec_apply, dotProduct, Fin.sum_univ_succ, Fin.succ_ne_zero, eq_comm]

end HodgeLean.Foundations.Abdulali
