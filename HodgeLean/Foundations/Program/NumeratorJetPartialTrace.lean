import HodgeLean.Foundations.Program.NumeratorJetQuotient

/-! # Partial traces of rational two-variable polynomial expressions -/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Evaluation of a rational two-variable polynomial at a pair of complex numbers. -/
def b65e_tensorEval (g : ℚ[X][X]) (x y : ℂ) : ℂ :=
  g.eval₂ (Polynomial.eval₂RingHom (Rat.castHom ℂ) x) y

/-- Reduction in the source-fibre variable. -/
def b65e_tensorReduce (e : Fin 2) (g : ℚ[X][X]) : ℚ[X][X] :=
  g %ₘ (b65e_fibrePolynomialQ e).map (C : ℚ →+* ℚ[X])

/-- Source reduction preserves evaluation on source-fibre roots. -/
theorem b65e_tensorReduce_eval (e : Fin 2) (g : ℚ[X][X]) (x y : ℂ)
    (hy : (b65q_fibreC e).eval y = 0) :
    b65e_tensorEval (b65e_tensorReduce e g) x y = b65e_tensorEval g x y := by
  apply Polynomial.eval₂_modByMonic_eq_self_of_root
  change ((b65e_fibrePolynomialQ e).map (C : ℚ →+* ℚ[X])).eval₂
    (Polynomial.eval₂RingHom (Rat.castHom ℂ) x) y = 0
  rw [Polynomial.eval₂_map]
  have he : (Polynomial.eval₂RingHom (Rat.castHom ℂ) x).comp (C : ℚ →+* ℚ[X]) =
      Rat.castHom ℂ := by
    ext a
    simp
  rw [he, ← Polynomial.eval_map, b65e_fibrePolynomialQ_map]
  exact hy

/-- Source reduction leaves fewer than six source-variable powers. -/
theorem b65e_tensorReduce_natDegree (e : Fin 2) (g : ℚ[X][X]) :
    (b65e_tensorReduce e g).natDegree < 6 := by
  have hm := (b65e_fibrePolynomialQ_monic e).map (C : ℚ →+* ℚ[X])
  have hd : ((b65e_fibrePolynomialQ e).map (C : ℚ →+* ℚ[X])).natDegree = 6 := by
    rw [(b65e_fibrePolynomialQ_monic e).natDegree_map, b65e_fibrePolynomialQ_natDegree]
  rw [← hd]
  apply Polynomial.natDegree_modByMonic_lt g hm
  intro h
  rw [h, natDegree_one] at hd
  omega

/-- The partial trace remains a rational polynomial in the target variable. -/
def b65e_partialTraceQ (e : Fin 2) (g : ℚ[X][X]) : ℚ[X] :=
  ∑ j : Fin 6, (b65e_tensorReduce e g).coeff j * C (b65q_psumQ e j)

/-- Partial traces are the actual sums over the six source labels. -/
theorem b65e_partialTraceQ_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e : Fin 2) (g : ℚ[X][X]) (x : ℂ) :
    ∑ y ∈ b65q_fibreSet e, b65e_tensorEval g x (p y) =
      (b65e_partialTraceQ e g).eval₂ (Rat.castHom ℂ) x := by
  have he (y : Fin 12) (hy : y ∈ b65q_fibreSet e) :
      b65e_tensorEval g x (p y) = ∑ j : Fin 6,
        ((b65e_tensorReduce e g).coeff j).eval₂ (Rat.castHom ℂ) x * p y ^ (j : ℕ) := by
    rw [← b65e_tensorReduce_eval e g x (p y) (b65q_fibre_root O e hy)]
    unfold b65e_tensorEval
    rw [Polynomial.eval₂_eq_sum_range' _ (b65e_tensorReduce_natDegree e g)]
    exact (Fin.sum_univ_eq_sum_range
      (fun t : ℕ ↦ ((b65e_tensorReduce e g).coeff t).eval₂ (Rat.castHom ℂ) x * p y ^ t) 6).symm
  rw [Finset.sum_congr rfl he, Finset.sum_comm]
  simp only [← Finset.mul_sum, b65q_psum O]
  simp only [b65e_partialTraceQ, eval₂_finsetSum, eval₂_mul, eval₂_C, Rat.coe_castHom]

end HodgeLean.Foundations.Program
