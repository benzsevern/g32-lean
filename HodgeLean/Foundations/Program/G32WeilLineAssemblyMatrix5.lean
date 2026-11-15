import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix4

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul26 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M24 w * g32c_M0 w = g32c_M25 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M24, g32c_M0, g32c_M25, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul27 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M25 w * g32c_M12 w = g32c_M26 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M25, g32c_M12, g32c_M26, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul28 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M26 w * g32c_M1 w = g32c_M27 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M26, g32c_M1, g32c_M27, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul29 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M1 w = g32c_M28 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M0, g32c_M1, g32c_M28, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul30 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M28 w * g32c_M16 w = g32c_M29 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M28, g32c_M16, g32c_M29, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul31 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M29 w * g32c_M0 w = g32c_M30 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M29, g32c_M0, g32c_M30, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
