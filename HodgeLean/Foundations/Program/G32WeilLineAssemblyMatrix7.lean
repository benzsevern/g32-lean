import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix6

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul38 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M0 w = g32c_M4 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M0, g32c_M0, g32c_M4, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul39 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M4 w * g32c_M1 w = g32c_M37 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M4, g32c_M1, g32c_M37, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul40 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M37 w * g32c_M0 w = g32c_M38 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M37, g32c_M0, g32c_M38, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul41 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M38 w * g32c_M0 w = g32c_M39 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M38, g32c_M0, g32c_M39, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul42 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M39 w * g32c_M40 w = g32c_M41 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M39, g32c_M40, g32c_M41, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul43 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M41 w * g32c_M42 w = g32c_M43 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M41, g32c_M42, g32c_M43, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
