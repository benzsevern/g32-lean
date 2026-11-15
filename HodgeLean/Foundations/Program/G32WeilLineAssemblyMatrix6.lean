import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix5

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_mul32 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M30 w * g32c_M1 w = g32c_M31 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M30, g32c_M1, g32c_M31, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul33 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M31 w * g32c_M12 w = g32c_M32 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M31, g32c_M12, g32c_M32, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul34 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M32 w * g32c_M16 w = g32c_M33 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M32, g32c_M16, g32c_M33, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul35 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M33 w * g32c_M10 w = g32c_M34 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M33, g32c_M10, g32c_M34, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul36 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M34 w * g32c_M0 w = g32c_M35 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M34, g32c_M0, g32c_M35, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

theorem g32c_mul37 (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M35 w * g32c_M16 w = g32c_M36 w := by
  have hp : w ^ 2 = -w - 1 := by linear_combination hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [g32c_M35, g32c_M16, g32c_M36, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hp] <;> ring

end HodgeLean.Foundations.Program
