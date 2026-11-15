import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.Defs
import HodgeLean.Foundations.Program.RiemannRochDefs

noncomputable section
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §13, degree as the sum of divisor coefficients. -/
theorem analyticDegree_weightedSum {C : Type} (D : C →₀ ℤ) :
    weightedSum (fun _ : C ↦ (1 : ℤ)) D = b4c_deg D := by
  simp only [weightedSum, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply,
    b4c_deg, zsmul_eq_mul, mul_one, Int.cast_id]


/-- Source: Forster, Lectures on Riemann Surfaces, §13, an effective divisor of degree zero is zero. -/
theorem divisor_eq_zero_of_nonneg_degree_zero {C : Type} (D : C →₀ ℤ)
    (hD : ∀ x, 0 ≤ D x) (hdeg : b4c_deg D = 0) : D = 0 := by
  classical
  have hs : ∑ x ∈ D.support, D x = 0 := hdeg
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ D.support
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ ↦ hD y)).mp hs x hx
  · exact Finsupp.notMem_support_iff.mp hx


end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
