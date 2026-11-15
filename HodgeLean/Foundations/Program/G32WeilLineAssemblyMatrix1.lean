import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix0

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul2 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M2 w * g32c_M2 w = g32c_M6 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M2, g32c_M2, g32c_M6, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul3 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M6 w * g32c_M2 w = g32c_M7 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M6, g32c_M2, g32c_M7, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_matrix_mul4 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M7 w * g32c_M2 w = g32c_M5 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M7, g32c_M2, g32c_M5, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul5 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M3 w = g32c_M8 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M3, g32c_M3, g32c_M8, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul6 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M8 w * g32c_M3 w = g32c_M5 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M8, g32c_M3, g32c_M5, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul7 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M2 w * g32c_M0 w = g32c_M9 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M2, g32c_M0, g32c_M9, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
