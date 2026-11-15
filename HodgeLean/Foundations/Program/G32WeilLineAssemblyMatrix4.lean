import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix3

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul20 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M18 w * g32c_M1 w = g32c_M19 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M18, g32c_M1, g32c_M19, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul21 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M19 w * g32c_M16 w = g32c_M20 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M19, g32c_M16, g32c_M20, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul22 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M20 w * g32c_M0 w = g32c_M21 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M20, g32c_M0, g32c_M21, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul23 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M21 w * g32c_M12 w = g32c_M22 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M21, g32c_M12, g32c_M22, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul24 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M22 w * g32c_M16 w = g32c_M23 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M22, g32c_M16, g32c_M23, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul25 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M23 w * g32c_M1 w = g32c_M24 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M23, g32c_M1, g32c_M24, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
