import Mathlib.RingTheory.NoetherNormalization
import Mathlib.Data.Real.Basic

/-! One polynomial coordinate automorphism gives unit leading coefficients for a finite family. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_common_polynomial_coordinates {n : ℕ}
    (S : Finset (MvPolynomial (Fin (n + 1)) ℝ)) (hS : ∀ p ∈ S, p ≠ 0) :
    ∃ T : MvPolynomial (Fin (n + 1)) ℝ ≃ₐ[ℝ] MvPolynomial (Fin (n + 1)) ℝ,
      ∀ p ∈ S, IsUnit (MvPolynomial.finSuccEquiv ℝ n (T p)).leadingCoeff := by
  classical
  let F := ∏ p ∈ S, p
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr hS
  let T := NoetherNormalization.varChange F
  refine ⟨T, ?_⟩
  have hunit := NoetherNormalization.varChange_leadingCoeff_isUnit F hF
  have hprod : IsUnit (∏ p ∈ S, (MvPolynomial.finSuccEquiv ℝ n (T p)).leadingCoeff) := by
    simpa only [F, map_prod, Polynomial.leadingCoeff_prod] using hunit
  intro p hp
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun q => (MvPolynomial.finSuccEquiv ℝ n (T q)).leadingCoeff) hp) hprod

end HodgeLean.Foundations.Program
