import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix1

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul8 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M9 w * g32c_M7 w = g32c_M10 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M9, g32c_M7, g32c_M10, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul9 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M0 w = g32c_M11 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M3, g32c_M0, g32c_M11, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul10 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M11 w * g32c_M8 w = g32c_M12 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M11, g32c_M8, g32c_M12, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul11 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M2 w = g32c_M13 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M3, g32c_M2, g32c_M13, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul12 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M13 w * g32c_M0 w = g32c_M14 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M13, g32c_M0, g32c_M14, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul13 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M14 w * g32c_M7 w = g32c_M15 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M14, g32c_M7, g32c_M15, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
