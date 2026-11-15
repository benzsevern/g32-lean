import HodgeLean.Foundations.Program.RigidStartingSystemEigenData

noncomputable section
open Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b65r_target_eigenbasis (w : ℂ) (hw : w^2+w+1=0) (i : Fin 4) :
    (![g32R1 w, g32R2 w, g32X w, g32Y w] i) * b65r_targetBasis w i =
      b65r_targetBasis w i * diagonal (b65r_localEigenvalues w i) := by
  have hw2 : w^2 = -w-1 := by linear_combination hw
  have hw3 : w^3 = 1 := (papers3b_omega_pow w hw).2.1
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [b65r_targetBasis, b65r_localEigenvalues, g32R1, g32R2, g32X, g32Y,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] <;>
    ring_nf <;> simp only [Complex.I_sq, hw2, hw3] <;> ring


end HodgeLean.Foundations.Program
