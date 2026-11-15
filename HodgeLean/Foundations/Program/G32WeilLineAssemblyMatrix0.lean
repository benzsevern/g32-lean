import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrixData

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_g32R1_matrix (w : ℂ) : g32R1 w = g32c_M0 w := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [g32R1, g32c_M0] <;> ring

theorem g32c_g32R2_matrix (w : ℂ) : g32R2 w = g32c_M1 w := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [g32R2, g32c_M1] <;> ring

theorem g32c_g32X_matrix (w : ℂ) : g32X w = g32c_M2 w := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [g32X, g32c_M2] <;> ring

theorem g32c_g32Y_matrix (w : ℂ) : g32Y w = g32c_M3 w := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [g32Y, g32c_M3] <;> ring

theorem g32c_mul0 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M0 w = g32c_M4 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M0, g32c_M0, g32c_M4, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul1 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M4 w * g32c_M0 w = g32c_M5 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M4, g32c_M0, g32c_M5, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
