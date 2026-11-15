import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Tactic

/-! # Linear representatives of coefficient jets -/
noncomputable section
set_option maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Every coefficient polynomial vanishing at the origin is linear modulo the square of the coordinate ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_coefficient_polynomial_linearization
    {R σ : Type*} [CommRing R] [Fintype σ]
    (p : MvPolynomial σ R) (hp : p ∈ idealOfVars σ R) :
    p - ∑ i, C (p.coeff (Finsupp.single i 1)) * X i ∈ idealOfVars σ R ^ 2 := by
  classical
  apply (mem_pow_idealOfVars_iff' 2 _).mpr
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hc : p.coeff 0 = 0 :=
      (mem_pow_idealOfVars_iff' 1 p).mp (by simpa only [pow_one] using hp) 0 (by simp)
    simp [coeff_sub, coeff_sum, coeff_C_mul, coeff_X, hc]
  · have hd : Finsupp.degree x = 1 := by
      have hn : Finsupp.degree x ≠ 0 := (Finsupp.degree_eq_zero_iff x).not.mpr hx0
      omega
    obtain ⟨i, rfl⟩ := (show x ∈ Set.range (fun i : σ => Finsupp.single i 1) by
      rw [Finsupp.range_single_one]; exact hd)
    simp [coeff_sub, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

/-- A quadratic term vanishes to first order while the linear term persists.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_coefficient_linearization_quadratic_check :
    ((X (0 : Fin 2) + X 1 ^ 2) - X 0 : MvPolynomial (Fin 2) ℚ) ∈
      idealOfVars (Fin 2) ℚ ^ 2 := by
  have h : (X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) ∈ idealOfVars (Fin 2) ℚ :=
    Ideal.subset_span ⟨1, rfl⟩
  convert Ideal.pow_mem_pow h 2 using 1 <;> ring

#print axioms s2e_coefficient_polynomial_linearization
#print axioms s2e_coefficient_linearization_quadratic_check
end HodgeLean.Foundations.Program
