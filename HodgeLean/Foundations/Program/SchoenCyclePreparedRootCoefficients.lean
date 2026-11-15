import HodgeLean.Foundations.AnalyticDivisorAlgebraic5
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Coefficients of prepared root tuples -/
noncomputable section
set_option maxHeartbeats 400000
open MvPolynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An enumeration of the prepared roots yields its exact signed block coefficients.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_prepared_root_tuple_coefficients
    {n d : ℕ} (c : Fin d → (Fin n → ℂ) → ℂ)
    (t : Fin n → ℂ) (z : Fin d → ℂ)
    (hz : monicPoly c t = ∏ i, (Polynomial.X - Polynomial.C (z i)))
    (j : Fin d) :
    c j t = (-1 : ℂ) ^ (d - j.val) *
      aeval z (esymm (Fin d) ℂ (d - j.val)) := by
  have hc : (monicPoly c t).coeff j.val = c j t := by
    simp only [monicPoly, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow]
    simp [j.isLt.ne, Fin.val_inj]
  rw [← hc, hz, aeval_esymm_eq_multiset_esymm]
  have hv := (Finset.univ.val.map z).prod_X_sub_C_coeff
    (k := j.val) (by simpa using j.isLt.le)
  simpa only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin,
    Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod] using hv

/-- Repetition changes the linear coefficient without removing the constant coefficient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_prepared_double_root_coefficients_check (z : ℂ) :
    ((Polynomial.X - Polynomial.C z) ^ 2 : Polynomial ℂ).coeff 0 = z ^ 2 ∧
    ((Polynomial.X - Polynomial.C z) ^ 2 : Polynomial ℂ).coeff 1 = -2 * z := by
  have he : ((Polynomial.X - Polynomial.C z) ^ 2 : Polynomial ℂ) =
      Polynomial.X ^ 2 - Polynomial.C (2 * z) * Polynomial.X + Polynomial.C (z ^ 2) := by
    simp only [map_mul, map_ofNat, map_pow]
    ring
  rw [he]
  norm_num only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C,
    ite_true, ite_false, one_mul, mul_one, mul_zero, zero_add, add_zero,
    sub_zero, zero_sub]
  exact ⟨trivial, by ring⟩

#print axioms s2e_prepared_root_tuple_coefficients
#print axioms s2e_prepared_double_root_coefficients_check
end HodgeLean.Foundations.Program
