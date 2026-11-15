import HodgeLean.Foundations.Program.NumeratorJetPolynomialCertificates

/-! # Reduced monomials and power moments through degree ten -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Monomial remainders needed for products of two sextic-coordinate arrays. -/
def b65e_powerReductionCoeffQ : Fin 11 → Fin 2 → Fin 6 → ℚ :=
  ![![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1]], ![![10, -15, (51/4), (-53/4), (69/4), (-27/4)], ![7, (-21/2), (-123/8), (185/8), (-33/8), (-9/8)]], ![![(-135/2), (445/4), (-1617/16), (1635/16), (-2075/16), (1005/16)], ![(-63/8), (301/16), (435/64), (-2649/64), (1777/64), (-183/64)]], ![![(5025/8), (-16155/16), (58375/64), (-59733/64), (75885/64), (-35435/64)], ![(-1281/64), (2835/128), (32141/512), (-30375/512), (-15153/512), (15863/512)]], ![![(-177175/32), (571725/64), (-2065665/256), (2111555/256), (-2683947/256), (1260285/256)], ![(111041/512), (-353619/1024), (-1860429/4096), (3191783/4096), (-766479/4096), (-263991/4096)]], ![![(6301425/128), (-20321675/256), (73422135/1024), (-75057765/1024), (95405885/1024), (-44763483/1024)], ![(-1847937/4096), (7320467/8192), (21155085/32768), (-63721767/32768), (34245967/32768), (-3755913/32768)]]]

/-- Reduced monomials as rational polynomials. -/
def b65e_powerReductionQ (n : Fin 11) (e : Fin 2) : ℚ[X] :=
  Polynomial.ofFn 6 (b65e_powerReductionCoeffQ n e)

/-- Coefficient vector of the coordinate polynomial. -/
def b65e_coordinateCoeffQ : Fin 6 → ℚ := ![0, 1, 0, 0, 0, 0]

/-- Multiplication by the coordinate has the listed reduced remainder. -/
theorem b65e_powerReduction_certificate (n : Fin 10) (e : Fin 2) :
    X * b65e_powerReductionQ n.castSucc e = b65e_powerReductionQ n.succ e +
      b65e_fibrePolynomialQ e * C (b65e_powerReductionCoeffQ n.castSucc e 5) := by
  have h := b65e_polynomial_mul_certificate b65e_coordinateCoeffQ
    (b65e_powerReductionCoeffQ n.castSucc e) (b65e_powerReductionCoeffQ n.succ e)
    (b65q_fibreCoeff e)
    (fun c : Fin 10 ↦ if c = 0 then b65e_powerReductionCoeffQ n.castSucc e 5 else 0)
    (by fin_cases n <;> fin_cases e <;> decide +kernel)
  simpa [b65e_coordinateCoeffQ, b65e_ofFn_eq_sum, b65e_powerReductionQ,
    b65e_fibrePolynomialQ, Fin.sum_univ_succ] using h

/-- The zeroth reduced monomial is one. -/
theorem b65e_powerReduction_zero (e : Fin 2) : b65e_powerReductionQ 0 e = 1 := by
  fin_cases e <;> simp [b65e_powerReductionQ, b65e_powerReductionCoeffQ,
    b65e_ofFn_eq_sum, Fin.sum_univ_succ]

/-- Reduced monomials evaluate to powers on every sextic root. -/
theorem b65e_powerReduction_eval (n : Fin 11) (e : Fin 2) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    (b65e_powerReductionQ n e).eval₂ (Rat.castHom ℂ) z = z ^ (n : ℕ) := by
  have hroot : (b65e_fibrePolynomialQ e).eval₂ (Rat.castHom ℂ) z = 0 := by
    rwa [← Polynomial.eval_map, b65e_fibrePolynomialQ_map]
  obtain ⟨n, hn⟩ := n
  induction n with
  | zero =>
    change (b65e_powerReductionQ 0 e).eval₂ (Rat.castHom ℂ) z = 1
    rw [b65e_powerReduction_zero, eval₂_one]
  | succ n ih =>
    have h := congrArg (fun g : ℚ[X] ↦ g.eval₂ (Rat.castHom ℂ) z)
      (b65e_powerReduction_certificate ⟨n, by omega⟩ e)
    simp only [eval₂_mul, eval₂_add, eval₂_X, hroot, zero_mul, add_zero] at h
    change z * (b65e_powerReductionQ ⟨n, by omega⟩ e).eval₂ (Rat.castHom ℂ) z =
      (b65e_powerReductionQ ⟨n + 1, hn⟩ e).eval₂ (Rat.castHom ℂ) z at h
    rw [← h, ih (by omega), pow_succ, mul_comm]

/-- Rational power moments through degree ten. -/
def b65e_powerMomentQ (n : Fin 11) (e : Fin 2) : ℚ :=
  ∑ c : Fin 6, b65e_powerReductionCoeffQ n e c * b65q_psumQ e c

/-- The rational power moments equal the labelled-root sums. -/
theorem b65e_powerMoment_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 11) (e : Fin 2) :
    ∑ x ∈ b65q_fibreSet e, p x ^ (n : ℕ) = (b65e_powerMomentQ n e : ℂ) := by
  apply b65q_fibre_reduce O e (fun z ↦ z ^ (n : ℕ))
    (b65e_powerReductionCoeffQ n e)
  intro z hz
  rw [← b65e_powerReduction_eval n e z hz]
  simp only [b65e_powerReductionQ, b65e_ofFn_eq_sum, eval₂_finsetSum,
    eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Rat.coe_castHom]

end HodgeLean.Foundations.Program
