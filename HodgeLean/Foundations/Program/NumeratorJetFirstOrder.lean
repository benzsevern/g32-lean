import HodgeLean.Foundations.Program.NumeratorJetRecurrence
import HodgeLean.Foundations.Program.KernelFramesFamilyRoots
import HodgeLean.Foundations.Program.NumeratorJetDefs

/-! # First fixed-pole coefficients from fibre moments -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Coefficients of the two velocity polynomials in ascending degree. -/
def b65e_velocityQ : Fin 2 → Fin 6 → ℚ :=
  ![![-2/7, 1/7, 3/7, 3/7, 3/7, -3/7], ![-1/7, -3/7, 0, 3/7, 0, 0]]

/-- The velocity coefficients evaluate to the path velocity. -/
theorem b65e_velocityQ_eval (e : Fin 2) (z : ℂ) :
    b65p_V (b65q_fibreValue e) z =
      ∑ c : Fin 6, (b65e_velocityQ e c : ℂ) * z ^ (c : ℕ) := by
  fin_cases e <;>
    norm_num [b65p_V, b65q_fibreValue, b65p_V5, b65p_Vneg7,
      b65e_velocityQ, Fin.sum_univ_succ] <;> ring

/-- Rational velocity moments about the four fixed poles. -/
def b65e_velocityMoment (e : Fin 2) (k : Fin 4) : ℚ :=
  ∑ c : Fin 6, b65e_velocityQ e c * b65q_DQ e k 1 c

/-- Weighted reciprocal sums obtained from the checked mixed fibre moments. -/
theorem b65e_velocityMoment_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e : Fin 2) (k : Fin 4) :
    ∑ x ∈ b65q_fibreSet e,
      b65p_V (b65q_fibreValue e) (p x) / (p x - b65p_fixedPole k) =
        (b65e_velocityMoment e k : ℂ) := by
  simp only [b65e_velocityQ_eval, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  unfold b65e_velocityMoment
  push_cast
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simpa only [pow_one] using b65q_DQ_sum O e k c 1 (by omega) (by omega)

/-- The first fixed-residue recursion evaluated over the rationals. -/
def b65e_fixedFirstQ (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℚ :=
  ∑ e : Fin 2, b65e_velocityMoment e k •
    (b65q_BQ e * b65q_fixedResQ k - b65q_fixedResQ k * b65q_BQ e)

/-- The stored first fixed-residue table agrees with the finite field recursion. -/
theorem b65e_fixedFirstQ_table : ∀ k : Fin 4,
    b65e_fixedFirstQ k = b65e_fixedJet 1 k := by
  decide +kernel

end HodgeLean.Foundations.Program
