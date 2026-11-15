import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix2

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul14 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M15 w * g32c_M8 w = g32c_M16 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M15, g32c_M8, g32c_M16, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul15 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M2 w * g32c_M2 w = g32c_M6 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M2, g32c_M2, g32c_M6, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul16 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M6 w * g32c_M2 w = g32c_M7 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M6, g32c_M2, g32c_M7, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul17 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M3 w = g32c_M8 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M3, g32c_M3, g32c_M8, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul18 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M12 w = g32c_M17 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M0, g32c_M12, g32c_M17, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul19 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M17 w * g32c_M16 w = g32c_M18 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M17, g32c_M16, g32c_M18, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
