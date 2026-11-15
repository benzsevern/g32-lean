import Mathlib.RingTheory.Polynomial.IsIntegral

noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

variable {R : Type*} [CommRing R]

def b54_polynomialScale (c : R) : R[X] →+* R[X] := eval₂RingHom C (C c * X)

theorem b54_polynomialScale_coeff (c : R) (p : R[X]) (n : ℕ) :
    (b54_polynomialScale c p).coeff n = c ^ n * p.coeff n := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]
  | monomial k a =>
    change (eval₂ C (C c * X) (monomial k a)).coeff n = _
    rw [eval₂_monomial, mul_pow, ← map_pow, ← mul_assoc, ← map_mul,
      C_mul_X_pow_eq_monomial]
    simp only [coeff_monomial]
    by_cases h : k = n
    · subst n; simp [mul_comm]
    · simp [h]

end HodgeLean.Foundations.Program
