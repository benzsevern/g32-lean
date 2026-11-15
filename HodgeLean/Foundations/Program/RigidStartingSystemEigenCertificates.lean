import HodgeLean.Foundations.Program.RigidStartingSystemEigenData

noncomputable section
open Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b65r_source_basis_inverse (i : Fin 4) :
    b65r_sourceBasis i * b65r_sourceInverse i = 1 := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [b65r_sourceBasis, b65r_sourceInverse, Matrix.mul_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 400000 in
theorem b65r_target_basis_inverse (w : ℂ) (hw : w^2+w+1=0) (i : Fin 4) :
    b65r_targetBasis w i * b65r_targetInverse w i = 1 := by
  have hw2 : w^2 = -w-1 := by linear_combination hw
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [b65r_targetBasis, b65r_targetInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [Complex.I_sq, hw2] <;> ring

set_option maxHeartbeats 400000 in
theorem b65r_source_eigenbasis (i : Fin 4) :
    b65r_residues i * b65r_sourceBasis i =
      b65r_sourceBasis i * diagonal (b65r_eigenvalues i) := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [b65r_residues, b65r_sourceBasis, b65r_eigenvalues, b65r_B0,
      b65r_B5, b65r_Bneg7, b65r_Binf, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]

end HodgeLean.Foundations.Program
