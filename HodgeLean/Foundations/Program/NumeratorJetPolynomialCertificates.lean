import HodgeLean.Foundations.Program.NumeratorJetCrossInverse
import Mathlib.Algebra.Polynomial.OfFn

/-! # Finite rational coefficient certificates for polynomial identities -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- The zero extension of a finite rational coefficient vector. -/
def b65e_vectorCoeffQ {d : ℕ} (v : Fin d → ℚ) (n : ℕ) : ℚ :=
  if h : n < d then v ⟨n, h⟩ else 0

/-- Finite polynomial encoding agrees with the sum of coefficient monomials. -/
theorem b65e_ofFn_eq_sum {d : ℕ} (v : Fin d → ℚ) :
    Polynomial.ofFn d v = ∑ c : Fin d, C (v c) * X ^ (c : ℕ) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [← C_mul_X_pow_eq_monomial]

/-- Coefficients of the finite encoding are the zero-extended vector. -/
theorem b65e_ofFn_coeff {d : ℕ} (v : Fin d → ℚ) (n : ℕ) :
    (Polynomial.ofFn d v).coeff n = b65e_vectorCoeffQ v n := by
  unfold b65e_vectorCoeffQ
  split_ifs with h
  · exact Polynomial.ofFn_coeff_eq_val_of_lt v h
  · exact Polynomial.ofFn_coeff_eq_zero_of_ge v (by omega)

/-- A degree-fifteen polynomial identity follows from sixteen rational coefficient checks. -/
theorem b65e_polynomial_mul_certificate (u v r : Fin 6 → ℚ)
    (s : Fin 7 → ℚ) (q : Fin 10 → ℚ)
    (h : ∀ n : Fin 16,
      (∑ a ∈ Finset.range (n.val + 1),
        b65e_vectorCoeffQ u a * b65e_vectorCoeffQ v (n.val - a)) =
      b65e_vectorCoeffQ r n.val +
      (∑ a ∈ Finset.range (n.val + 1),
        b65e_vectorCoeffQ s a * b65e_vectorCoeffQ q (n.val - a))) :
    Polynomial.ofFn 6 u * Polynomial.ofFn 6 v =
      Polynomial.ofFn 6 r + Polynomial.ofFn 7 s * Polynomial.ofFn 10 q := by
  have h6 (w : Fin 6 → ℚ) : (Polynomial.ofFn 6 w).natDegree ≤ 5 := by
    have := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ 6) w
    omega
  have h7 : (Polynomial.ofFn 7 s).natDegree ≤ 6 := by
    have := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ 7) s
    omega
  have h10 : (Polynomial.ofFn 10 q).natDegree ≤ 9 := by
    have := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ 10) q
    omega
  have hl : (Polynomial.ofFn 6 u * Polynomial.ofFn 6 v).natDegree ≤ 15 :=
    (natDegree_mul_le_of_le (h6 u) (h6 v)).trans (by omega)
  have hr : (Polynomial.ofFn 6 r + Polynomial.ofFn 7 s * Polynomial.ofFn 10 q).natDegree ≤ 15 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (h6 r).trans (by omega)
    · exact natDegree_mul_le_of_le h7 h10
  apply (Polynomial.ext_iff_natDegree_le (n := 15) hl hr).2
  intro n hn
  rw [coeff_add, b65e_cross_mul_coeff, b65e_cross_mul_coeff]
  simp only [b65e_ofFn_coeff]
  exact h ⟨n, by omega⟩

end HodgeLean.Foundations.Program
