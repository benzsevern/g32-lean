import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix7

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul44 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M43 w * g32c_M42 w = g32c_M44 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M43, g32c_M42, g32c_M44, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul45 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M1 w * g32c_M1 w = g32c_M45 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M1, g32c_M1, g32c_M45, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul46 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M0 w = g32c_M4 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M0, g32c_M0, g32c_M4, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul47 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M1 w * g32c_M1 w = g32c_M45 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M1, g32c_M1, g32c_M45, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul48 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M45 w * g32c_M1 w = g32c_M5 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M45, g32c_M1, g32c_M5, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_identity_matrix (w : ℂ) : g32c_M46 w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [g32c_M46]

end HodgeLean.Foundations.Program
