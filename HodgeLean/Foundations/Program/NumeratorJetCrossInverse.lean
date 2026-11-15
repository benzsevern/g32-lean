import HodgeLean.Foundations.Program.NumeratorJetDividedDifference

/-! # Polynomial inverse certificates for interactions between distinct fibres -/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The fibre opposite to the given one. -/
def b65e_otherFibre (e : Fin 2) : Fin 2 := if e = 0 then 1 else 0

/-- Bezout inverse coefficients of the opposite sextic, modulo the given sextic. -/
def b65e_crossInverseCoeffQ : Fin 2 → Fin 6 → ℚ :=
  ![![1313/7500, -71/1000, 5343/50000, -12793/75000, 4827/50000, 33/2500],
    ![-16691/75000, -1003/10000, 25311/100000, -10459/150000, -2229/100000, -33/2500]]

/-- Bezout inverse polynomial for the opposite sextic. -/
def b65e_crossInverseQ (e : Fin 2) : ℚ[X] :=
  ∑ i : Fin 6, C (b65e_crossInverseCoeffQ e i) * X ^ (i : ℕ)

/-- Product coefficients written as sums over a finite interval. -/
theorem b65e_cross_mul_coeff (f g : ℚ[X]) (n : ℕ) :
    (f * g).coeff n = ∑ i ∈ Finset.range (n + 1), f.coeff i * g.coeff (n - i) := by
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ f.coeff i * g.coeff j) n

set_option maxHeartbeats 400000 in
/-- The two rational Bezout polynomials give the identity polynomial. -/
theorem b65e_crossInverseQ_certificate :
    b65e_fibrePolynomialQ 1 * b65e_crossInverseQ 0 +
      b65e_fibrePolynomialQ 0 * b65e_crossInverseQ 1 = 1 := by
  norm_num [b65e_crossInverseQ, b65e_crossInverseCoeffQ,
    b65e_fibrePolynomialQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  apply (Polynomial.ext_iff_natDegree_le (n := 11) (by compute_degree <;> norm_num) (by compute_degree <;> norm_num)).2
  intro n hn
  interval_cases n <;> norm_num [b65e_cross_mul_coeff, Finset.sum_range_succ, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one, coeff_X]

/-- The same Bezout identity in either fibre order. -/
theorem b65e_crossInverseQ_certificate_ordered (e : Fin 2) :
    b65e_fibrePolynomialQ (b65e_otherFibre e) * b65e_crossInverseQ e +
      b65e_fibrePolynomialQ e * b65e_crossInverseQ (b65e_otherFibre e) = 1 := by
  fin_cases e
  · exact b65e_crossInverseQ_certificate
  · exact (add_comm _ _).trans b65e_crossInverseQ_certificate

/-- Evaluating Bezout on a fibre root inverts the opposite sextic value. -/
theorem b65e_crossInverseQ_eval_mul (e : Fin 2) (x : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) :
    (b65e_crossInverseQ e).eval₂ (Rat.castHom ℂ) x *
      (b65e_fibrePolynomialQ (b65e_otherFibre e)).eval₂ (Rat.castHom ℂ) x = 1 := by
  have hroot : (b65e_fibrePolynomialQ e).eval₂ (Rat.castHom ℂ) x = 0 := by
    rwa [← Polynomial.eval_map, b65e_fibrePolynomialQ_map]
  have h := congrArg (fun g : ℚ[X] ↦ g.eval₂ (Rat.castHom ℂ) x)
    (b65e_crossInverseQ_certificate_ordered e)
  simp only [eval₂_add, eval₂_mul, eval₂_one, hroot, zero_mul, add_zero] at h
  rwa [mul_comm]

/-- A polynomial expression for the cross-fibre reciprocal, with no division at roots. -/
theorem b65e_crossPole_inverse (e : Fin 2) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0)
    (hy : (b65q_fibreC (b65e_otherFibre e)).eval y = 0) :
    (b65e_crossInverseQ e).eval₂ (Rat.castHom ℂ) x *
      b65e_dividedDifference (b65e_fibrePolynomialQ (b65e_otherFibre e)) x y =
      (x - y)⁻¹ := by
  have hroot : (b65e_fibrePolynomialQ (b65e_otherFibre e)).eval₂ (Rat.castHom ℂ) y = 0 := by
    rwa [← Polynomial.eval_map, b65e_fibrePolynomialQ_map]
  apply eq_inv_of_mul_eq_one_left
  rw [mul_assoc, b65e_dividedDifference_mul, hroot, sub_zero]
  exact b65e_crossInverseQ_eval_mul e x hx

end HodgeLean.Foundations.Program
