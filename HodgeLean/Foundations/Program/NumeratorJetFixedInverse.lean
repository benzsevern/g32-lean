import HodgeLean.Foundations.Program.NumeratorJetQuotient

/-! # Rational certificates for fixed-pole inverses in the sextic quotients -/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Rational coordinates of the four fixed poles. -/
def b65e_fixedPoleQ : Fin 4 → ℚ := ![0, 3, 1, -2]

/-- Rational and complex fixed-pole coordinates agree. -/
theorem b65e_fixedPoleQ_cast (k : Fin 4) :
    (b65e_fixedPoleQ k : ℂ) = b65p_fixedPole k := by
  fin_cases k <;> norm_num [b65e_fixedPoleQ, b65p_fixedPole]

/-- Inverse coefficients in increasing powers of the sextic coordinate. -/
def b65e_fixedInverseCoeffQ : Fin 2 → Fin 4 → Fin 6 → ℚ :=
  ![![![3/2, -51/40, 53/40, -69/40, 27/40, 1/10],
    ![-42/125, -27/250, -197/5000, -6/625, -39/5000, -1/1250],
    ![3/2, -9/4, 15/16, -19/8, 31/16, 1/4],
    ![123/250, -117/500, 267/2500, -107/2500, 19/2500, 1/625]],
    ![![3/2, 123/56, -185/56, 33/56, 9/56, 1/7],
    ![-42/125, -27/250, -211/7000, -33/1750, -33/7000, -1/875],
    ![-9/2, 3/4, 135/16, -25/8, -17/16, -1/2],
    ![639/1250, -681/2500, 279/2500, -47/2500, 7/2500, -2/625]]]

/-- Polynomial representing the reciprocal of the displacement from a fixed pole. -/
def b65e_fixedInverseQ (e : Fin 2) (k : Fin 4) : ℚ[X] :=
  ∑ i : Fin 6, C (b65e_fixedInverseCoeffQ e k i) * X ^ (i : ℕ)

/-- Rational polynomial identity for fibre 0 and fixed pole 0. -/
theorem b65e_fixedInverseQ_certificate_0_0 :
    (X - C (b65e_fixedPoleQ 0)) * b65e_fixedInverseQ 0 0 =
      1 - C (((b65e_fibrePolynomialQ 0).eval (b65e_fixedPoleQ 0))⁻¹) *
        b65e_fibrePolynomialQ 0 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Rational polynomial identity for fibre 0 and fixed pole 1. -/
theorem b65e_fixedInverseQ_certificate_0_1 :
    (X - C (b65e_fixedPoleQ 1)) * b65e_fixedInverseQ 0 1 =
      1 - C (((b65e_fibrePolynomialQ 0).eval (b65e_fixedPoleQ 1))⁻¹) *
        b65e_fibrePolynomialQ 0 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Rational polynomial identity for fibre 0 and fixed pole 2. -/
theorem b65e_fixedInverseQ_certificate_0_2 :
    (X - C (b65e_fixedPoleQ 2)) * b65e_fixedInverseQ 0 2 =
      1 - C (((b65e_fibrePolynomialQ 0).eval (b65e_fixedPoleQ 2))⁻¹) *
        b65e_fibrePolynomialQ 0 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Rational polynomial identity for fibre 0 and fixed pole 3. -/
theorem b65e_fixedInverseQ_certificate_0_3 :
    (X - C (b65e_fixedPoleQ 3)) * b65e_fixedInverseQ 0 3 =
      1 - C (((b65e_fibrePolynomialQ 0).eval (b65e_fixedPoleQ 3))⁻¹) *
        b65e_fibrePolynomialQ 0 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Rational polynomial identity for fibre 1 and fixed pole 0. -/
theorem b65e_fixedInverseQ_certificate_1_0 :
    (X - C (b65e_fixedPoleQ 0)) * b65e_fixedInverseQ 1 0 =
      1 - C (((b65e_fibrePolynomialQ 1).eval (b65e_fixedPoleQ 0))⁻¹) *
        b65e_fibrePolynomialQ 1 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Rational polynomial identity for fibre 1 and fixed pole 1. -/
theorem b65e_fixedInverseQ_certificate_1_1 :
    (X - C (b65e_fixedPoleQ 1)) * b65e_fixedInverseQ 1 1 =
      1 - C (((b65e_fibrePolynomialQ 1).eval (b65e_fixedPoleQ 1))⁻¹) *
        b65e_fibrePolynomialQ 1 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Rational polynomial identity for fibre 1 and fixed pole 2. -/
theorem b65e_fixedInverseQ_certificate_1_2 :
    (X - C (b65e_fixedPoleQ 2)) * b65e_fixedInverseQ 1 2 =
      1 - C (((b65e_fibrePolynomialQ 1).eval (b65e_fixedPoleQ 2))⁻¹) *
        b65e_fibrePolynomialQ 1 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Rational polynomial identity for fibre 1 and fixed pole 3. -/
theorem b65e_fixedInverseQ_certificate_1_3 :
    (X - C (b65e_fixedPoleQ 3)) * b65e_fixedInverseQ 1 3 =
      1 - C (((b65e_fibrePolynomialQ 1).eval (b65e_fixedPoleQ 3))⁻¹) *
        b65e_fibrePolynomialQ 1 := by
  norm_num [b65e_fixedInverseQ, b65e_fixedInverseCoeffQ, b65e_fibrePolynomialQ,
    b65e_fixedPoleQ, b65q_fibreCoeff, Fin.sum_univ_succ]
  ring_nf
  apply (Polynomial.ext_iff_natDegree_le (n := 6) (by compute_degree) (by compute_degree)).2
  intro n hn
  interval_cases n <;> norm_num [← C_mul, coeff_C_mul_X_pow, coeff_mul_C, coeff_C_mul, coeff_one]

/-- Each listed inverse satisfies a rational polynomial identity with the sextic. -/
theorem b65e_fixedInverseQ_certificate : ∀ e : Fin 2, ∀ k : Fin 4,
    (X - C (b65e_fixedPoleQ k)) * b65e_fixedInverseQ e k =
      1 - C (((b65e_fibrePolynomialQ e).eval (b65e_fixedPoleQ k))⁻¹) *
        b65e_fibrePolynomialQ e := by
  intro e k
  fin_cases e <;> fin_cases k
  · exact b65e_fixedInverseQ_certificate_0_0
  · exact b65e_fixedInverseQ_certificate_0_1
  · exact b65e_fixedInverseQ_certificate_0_2
  · exact b65e_fixedInverseQ_certificate_0_3
  · exact b65e_fixedInverseQ_certificate_1_0
  · exact b65e_fixedInverseQ_certificate_1_1
  · exact b65e_fixedInverseQ_certificate_1_2
  · exact b65e_fixedInverseQ_certificate_1_3

/-- The inverse certificates evaluate to reciprocals at every root of a fibre sextic. -/
theorem b65e_fixedInverseQ_eval (e : Fin 2) (k : Fin 4) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    (b65e_fixedInverseQ e k).eval₂ (Rat.castHom ℂ) z =
      (z - b65p_fixedPole k)⁻¹ := by
  have hroot : (b65e_fibrePolynomialQ e).eval₂ (Rat.castHom ℂ) z = 0 := by
    rwa [← Polynomial.eval_map, b65e_fibrePolynomialQ_map]
  have h := congrArg (fun g : ℚ[X] ↦ g.eval₂ (Rat.castHom ℂ) z)
    (b65e_fixedInverseQ_certificate e k)
  simp only [eval₂_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C,
    Rat.coe_castHom, b65e_fixedPoleQ_cast, hroot, mul_zero, sub_zero] at h
  exact eq_inv_of_mul_eq_one_right h

/-- All powers of fixed-pole denominators reduce to the rational quotient trace. -/
theorem b65e_fixedInverseQ_trace (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e : Fin 2) (k : Fin 4) (g : ℚ[X]) (m : ℕ) :
    ∑ x ∈ b65q_fibreSet e, g.eval₂ (Rat.castHom ℂ) (p x) /
      (p x - b65p_fixedPole k) ^ m =
      (b65e_fibreTraceQ e (g * b65e_fixedInverseQ e k ^ m) : ℂ) := by
  rw [← b65e_fibreTraceQ_sum p O e]
  apply Finset.sum_congr rfl
  intro x hx
  rw [eval₂_mul, eval₂_pow, b65e_fixedInverseQ_eval e k (p x) (b65q_fibre_root O e hx)]
  simp only [div_eq_mul_inv, inv_pow]

end HodgeLean.Foundations.Program
