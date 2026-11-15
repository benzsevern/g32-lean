import HodgeLean.Foundations.Program.RigidStartingSystemDefs

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b65r_B5_quadratic : b65r_B5 * b65r_B5 = (1/3 : ℂ) • b65r_B5 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, b65r_B5]

set_option maxHeartbeats 400000 in
theorem b65r_Bneg7_quadratic : b65r_Bneg7 * b65r_Bneg7 = (2/3 : ℂ) • b65r_Bneg7 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, b65r_Bneg7]

set_option maxHeartbeats 400000 in
theorem b65r_Binf_quadratic : b65r_Binf * b65r_Binf = (4/9 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, b65r_Binf, b65r_B0,
      b65r_B5, b65r_Bneg7, Matrix.diagonal]

end HodgeLean.Foundations.Program
