import HodgeLean.Foundations.Program.NumeratorJetFirstOrder

/-! # Rational sextic reduction and traces on the labelled fibres -/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The two monic sextics over the rationals. -/
def b65e_fibrePolynomialQ (e : Fin 2) : ℚ[X] :=
  ∑ i : Fin 7, C (b65q_fibreCoeff e i) * X ^ (i : ℕ)

/-- Casting the rational sextics recovers the fibre polynomials used by the record. -/
theorem b65e_fibrePolynomialQ_map (e : Fin 2) :
    (b65e_fibrePolynomialQ e).map (Rat.castHom ℂ) = b65q_fibreC e := by
  rw [b65q_fibreC_eq]
  simp only [b65e_fibrePolynomialQ, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Rat.coe_castHom]

/-- Rational sextic reduction uses a monic divisor. -/
theorem b65e_fibrePolynomialQ_monic (e : Fin 2) : (b65e_fibrePolynomialQ e).Monic := by
  apply (Polynomial.monic_map_iff (f := Rat.castHom ℂ)).mp
  rw [b65e_fibrePolynomialQ_map]
  exact b65q_fibreC_monic e

/-- The rational sextic degree is six. -/
theorem b65e_fibrePolynomialQ_natDegree (e : Fin 2) :
    (b65e_fibrePolynomialQ e).natDegree = 6 := by
  rw [← (b65e_fibrePolynomialQ_monic e).natDegree_map (Rat.castHom ℂ),
    b65e_fibrePolynomialQ_map, b65q_fibreC_natDegree]

/-- Evaluation at a sextic root is unchanged by rational remainder reduction. -/
theorem b65e_fibre_mod_eval (e : Fin 2) (g : ℚ[X]) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    (g %ₘ b65e_fibrePolynomialQ e).eval₂ (Rat.castHom ℂ) z =
      g.eval₂ (Rat.castHom ℂ) z := by
  apply Polynomial.eval₂_modByMonic_eq_self_of_root
  rwa [← Polynomial.eval_map, b65e_fibrePolynomialQ_map]

/-- Reduced rational polynomials have at most six coefficient positions. -/
theorem b65e_fibre_mod_natDegree (e : Fin 2) (g : ℚ[X]) :
    (g %ₘ b65e_fibrePolynomialQ e).natDegree < 6 := by
  rw [← b65e_fibrePolynomialQ_natDegree e]
  apply Polynomial.natDegree_modByMonic_lt g (b65e_fibrePolynomialQ_monic e)
  intro h
  have := b65e_fibrePolynomialQ_natDegree e
  rw [h, Polynomial.natDegree_one] at this
  omega

/-- The six reduced coefficients give the value on every root of the sextic. -/
theorem b65e_fibre_mod_eval_sum (e : Fin 2) (g : ℚ[X]) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    g.eval₂ (Rat.castHom ℂ) z = ∑ i : Fin 6,
      ((g %ₘ b65e_fibrePolynomialQ e).coeff i : ℂ) * z ^ (i : ℕ) := by
  rw [← b65e_fibre_mod_eval e g z hz]
  rw [Polynomial.eval₂_eq_sum_range' (Rat.castHom ℂ) (b65e_fibre_mod_natDegree e g) z]
  exact (Fin.sum_univ_eq_sum_range
    (fun t : ℕ ↦ (Rat.castHom ℂ) ((g %ₘ b65e_fibrePolynomialQ e).coeff t) * z ^ t) 6).symm

/-- The rational trace functional on the sextic quotient. -/
def b65e_fibreTraceQ (e : Fin 2) (g : ℚ[X]) : ℚ :=
  ∑ i : Fin 6, (g %ₘ b65e_fibrePolynomialQ e).coeff i * b65q_psumQ e i

/-- Rational quotient traces equal the sum over the record's labelled roots. -/
theorem b65e_fibreTraceQ_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e : Fin 2) (g : ℚ[X]) :
    ∑ x ∈ b65q_fibreSet e, g.eval₂ (Rat.castHom ℂ) (p x) =
      (b65e_fibreTraceQ e g : ℂ) := by
  exact b65q_fibre_reduce O e (fun z ↦ g.eval₂ (Rat.castHom ℂ) z)
    (fun i ↦ (g %ₘ b65e_fibrePolynomialQ e).coeff i)
    (fun z hz ↦ b65e_fibre_mod_eval_sum e g z hz)

end HodgeLean.Foundations.Program
