import HodgeLean.Foundations.Program.RigidStartingSystemIrreducibleData

noncomputable section
open Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b65r_cyclic_columns_inverse (w : ℂ) (hw : w^2+w+1=0) :
    b65r_cyclicColumns w * b65r_cyclicColumnsInverse w = 1 := by
  have hw2 : w^2 = -w-1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [b65r_cyclicColumns, b65r_cyclicColumnsInverse, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring_nf <;> simp only [hw2] <;> ring

set_option maxHeartbeats 400000 in
theorem b65r_cyclic_rows_inverse (w : ℂ) (hw : w^2+w+1=0) :
    b65r_cyclicRows w * b65r_cyclicRowsInverse w = 1 := by
  have hw2 : w^2 = -w-1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [b65r_cyclicRows, b65r_cyclicRowsInverse, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring_nf <;> simp only [hw2] <;> ring

set_option maxHeartbeats 400000 in
theorem b65r_cyclic_columns (w : ℂ) (hw : w^2+w+1=0) (i : Fin 4) :
    (b65r_cyclicColumns w)ᵀ i =
      (b65r_leftWords w i).mulVec (b65r_reflectionVector w) := by
  have hw2 : w^2 = -w-1 := by linear_combination hw
  have hw3 : w^3 = 1 := (papers3b_omega_pow w hw).2.1
  fin_cases i
  · change (b65r_cyclicColumns w)ᵀ 0 = (1 : Matrix (Fin 4) (Fin 4) ℂ).mulVec _
    rw [one_mulVec]
    ext j
    fin_cases j <;> rfl
  · change (b65r_cyclicColumns w)ᵀ 1 = (g32R2 w).mulVec _
    ext j
    fin_cases j <;>
      norm_num [b65r_cyclicColumns, b65r_reflectionVector, g32R2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hw2, hw3] <;> ring
  · change (b65r_cyclicColumns w)ᵀ 2 = (g32X w).mulVec _
    ext j
    fin_cases j <;>
      norm_num [b65r_cyclicColumns, b65r_reflectionVector, g32X,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hw2, hw3] <;> ring
  · change (b65r_cyclicColumns w)ᵀ 3 = (g32X w * g32R2 w).mulVec _
    rw [← mulVec_mulVec]
    ext j
    fin_cases j <;>
      norm_num [b65r_cyclicColumns, b65r_reflectionVector, g32R2, g32X,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hw2, hw3] <;> ring

set_option maxHeartbeats 400000 in
theorem b65r_cyclic_rows (w : ℂ) (hw : w^2+w+1=0) (i : Fin 4) :
    b65r_cyclicRows w i = Matrix.vecMul (b65r_reflectionRow w) (b65r_rightWords w i) := by
  have hw2 : w^2 = -w-1 := by linear_combination hw
  have hw3 : w^3 = 1 := (papers3b_omega_pow w hw).2.1
  fin_cases i
  · change b65r_cyclicRows w 0 = Matrix.vecMul (b65r_reflectionRow w) (1 : Matrix (Fin 4) (Fin 4) ℂ)
    rw [vecMul_one]
    ext j
    fin_cases j <;> norm_num [b65r_cyclicRows, b65r_reflectionRow] <;> ring
  · change b65r_cyclicRows w 1 = Matrix.vecMul (b65r_reflectionRow w) (g32R2 w)
    ext j
    fin_cases j <;>
      norm_num [b65r_cyclicRows, b65r_reflectionRow, g32R2, Matrix.vecMul,
        dotProduct, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hw2, hw3] <;> ring
  · change b65r_cyclicRows w 2 = Matrix.vecMul (b65r_reflectionRow w) (g32X w)
    ext j
    fin_cases j <;>
      norm_num [b65r_cyclicRows, b65r_reflectionRow, g32X, Matrix.vecMul,
        dotProduct, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hw2, hw3] <;> ring
  · change b65r_cyclicRows w 3 = Matrix.vecMul (b65r_reflectionRow w) (g32R2 w * g32X w)
    rw [← vecMul_vecMul]
    ext j
    fin_cases j <;>
      norm_num [b65r_cyclicRows, b65r_reflectionRow, g32R2, g32X, Matrix.vecMul,
        dotProduct, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hw2, hw3] <;> ring

set_option maxHeartbeats 400000 in
theorem b65r_reflection_rank_one (w : ℂ) (hw : w^2+w+1=0) :
    g32R1 w - 1 = vecMulVec (b65r_reflectionVector w) (b65r_reflectionRow w) := by
  have hw2 : w^2 = -w-1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32R1, b65r_reflectionVector, b65r_reflectionRow, vecMulVec,
      Matrix.one_apply] <;> ring_nf <;> simp only [hw2] <;> ring

end HodgeLean.Foundations.Program
