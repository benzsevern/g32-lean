import HodgeLean.Foundations.Program.RigidStartingSystemEigenData
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b65r_exp_third :
    Complex.exp ((2*Real.pi*Complex.I)*(1/3 : ℂ)) = g32h_omega := by
  unfold g32h_omega
  congr 1
  ring

theorem b65r_exp_twothirds :
    Complex.exp ((2*Real.pi*Complex.I)*(2/3 : ℂ)) = g32h_omega^2 := by
  rw [show (2*Real.pi*Complex.I)*(2/3 : ℂ) =
    (2 : ℕ)*((2*Real.pi*Complex.I)*(1/3 : ℂ)) by norm_num; ring,
    Complex.exp_nat_mul, b65r_exp_third]

theorem b65r_exp_neg_twothirds :
    Complex.exp ((2*Real.pi*Complex.I)*(-2/3 : ℂ)) = g32h_omega := by
  rw [show (2*Real.pi*Complex.I)*(-2/3 : ℂ) =
    (2*Real.pi*Complex.I)*(1/3 : ℂ) - (2*Real.pi*Complex.I) by ring,
    Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one, b65r_exp_third]

theorem b65r_exp_quarters :
    Complex.exp ((2*Real.pi*Complex.I)*(-3/4 : ℂ)) = Complex.I ∧
    Complex.exp ((2*Real.pi*Complex.I)*(-1/2 : ℂ)) = -1 ∧
    Complex.exp ((2*Real.pi*Complex.I)*(3/4 : ℂ)) = -Complex.I := by
  constructor
  · rw [show (2*Real.pi*Complex.I)*(-3/4 : ℂ) =
      (Real.pi : ℂ)/2*Complex.I - 2*Real.pi*Complex.I by ring,
      Complex.exp_sub, Complex.exp_pi_div_two_mul_I, Complex.exp_two_pi_mul_I, div_one]
  constructor
  · rw [show (2*Real.pi*Complex.I)*(-1/2 : ℂ) = -((Real.pi : ℂ)*Complex.I) by ring,
      Complex.exp_neg_pi_mul_I]
  · rw [show (2*Real.pi*Complex.I)*(3/4 : ℂ) =
      2*Real.pi*Complex.I + (-(Real.pi : ℂ)/2*Complex.I) by ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_neg_pi_div_two_mul_I, one_mul]

theorem b65r_scalar_exponential (i j : Fin 4) :
    NormedSpace.exp ((2*Real.pi*Complex.I)*b65r_eigenvalues i j) =
      b65r_localEigenvalues g32h_omega i j := by
  rw [← Complex.exp_eq_exp_ℂ]
  fin_cases i <;> fin_cases j <;>
    first | exact b65r_exp_third | exact b65r_exp_twothirds |
      exact b65r_exp_neg_twothirds | exact b65r_exp_quarters.1 |
      exact b65r_exp_quarters.2.1 | exact b65r_exp_quarters.2.2 |
      norm_num [b65r_eigenvalues, b65r_localEigenvalues]

end HodgeLean.Foundations.Program
