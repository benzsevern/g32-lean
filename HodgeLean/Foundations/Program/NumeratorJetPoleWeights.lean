import HodgeLean.Foundations.Program.NumeratorJetCrossInverse
import HodgeLean.Foundations.Program.NumeratorJetPartialTrace
import HodgeLean.Foundations.Program.NumeratorJetFixedInverse

/-! # Polynomial weights for the residue field -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Tensor evaluation preserves multiplication. -/
theorem b65e_tensorEval_mul (f g : ℚ[X][X]) (x y : ℂ) :
    b65e_tensorEval (f * g) x y = b65e_tensorEval f x y * b65e_tensorEval g x y := by
  exact Polynomial.eval₂_mul _ _

/-- Tensor evaluation of a target-variable polynomial. -/
theorem b65e_tensorEval_C (g : ℚ[X]) (x y : ℂ) :
    b65e_tensorEval (C g) x y = g.eval₂ (Rat.castHom ℂ) x := by
  exact Polynomial.eval₂_C _ _

/-- The polynomial divided difference in the target and source variables. -/
def b65e_tensorDifferenceQ (g : ℚ[X]) : ℚ[X][X] :=
  ∑ n ∈ Finset.range (g.natDegree + 1),
    C (C (g.coeff n)) * ∑ i ∈ Finset.range n,
      C (X ^ i) * X ^ (n - 1 - i)

/-- Evaluating the polynomial divided difference gives its scalar expression. -/
theorem b65e_tensorDifferenceQ_eval (g : ℚ[X]) (x y : ℂ) :
    b65e_tensorEval (b65e_tensorDifferenceQ g) x y = b65e_dividedDifference g x y := by
  simp only [b65e_tensorEval, b65e_tensorDifferenceQ, b65e_dividedDifference,
    eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    coe_eval₂RingHom, Rat.coe_castHom]

/-- Degrees of the two rational velocity polynomials. -/
theorem b65e_velocityPolynomialQ_natDegree (e : Fin 2) :
    (b65e_velocityPolynomialQ e).natDegree = if e = 0 then 5 else 3 := by
  fin_cases e <;> norm_num [b65e_velocityPolynomialQ, b65e_velocityQ, Fin.sum_univ_succ] <;>
    compute_degree <;> norm_num

/-- A polynomial reciprocal displacement between the two different fibres. -/
def b65e_tensorInverseQ (e : Fin 2) : ℚ[X][X] :=
  C (b65e_crossInverseQ e) *
    b65e_tensorDifferenceQ (b65e_fibrePolynomialQ (b65e_otherFibre e))

/-- Evaluation of the reciprocal polynomial on the two fibres. -/
theorem b65e_tensorInverseQ_eval (e : Fin 2) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0)
    (hy : (b65q_fibreC (b65e_otherFibre e)).eval y = 0) :
    b65e_tensorEval (b65e_tensorInverseQ e) x y = (x - y)⁻¹ := by
  rw [b65e_tensorInverseQ, b65e_tensorEval_mul, b65e_tensorEval_C,
    b65e_tensorDifferenceQ_eval]
  exact b65e_crossPole_inverse e x y hx hy

/-- Polynomial weights of the moving-to-moving pole ratio at the centre. -/
def b65e_tensorWeightQ (e d : Fin 2) : ℚ[X][X] :=
  if d = e then b65e_tensorDifferenceQ (b65e_velocityPolynomialQ e) else
    C (b65e_velocityPolynomialQ e - b65e_velocityPolynomialQ d) * b65e_tensorInverseQ e +
      b65e_tensorDifferenceQ (b65e_velocityPolynomialQ d)

/-- Distinct fibres have opposite indices. -/
theorem b65e_otherFibre_eq (e d : Fin 2) (h : d ≠ e) : b65e_otherFibre e = d := by
  fin_cases e <;> fin_cases d <;> simp_all [b65e_otherFibre]

/-- The polynomial moving-pole weight evaluates to the actual off-diagonal ratio. -/
theorem b65e_tensorWeightQ_eval (e d : Fin 2) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) (hy : (b65q_fibreC d).eval y = 0)
    (hxy : x ≠ y) :
    b65e_tensorEval (b65e_tensorWeightQ e d) x y =
      (b65p_V (b65q_fibreValue e) x - b65p_V (b65q_fibreValue d) y) / (x - y) := by
  by_cases h : d = e
  · subst d
    rw [b65e_tensorWeightQ, ite_eq_left rfl, b65e_tensorDifferenceQ_eval,
      b65e_dividedDifference_eq_div _ _ _ hxy,
      b65e_velocityPolynomialQ_eval, b65e_velocityPolynomialQ_eval]
  · rw [b65e_tensorWeightQ, ite_eq_right h]
    have hi := b65e_tensorInverseQ_eval e x y hx (by rwa [b65e_otherFibre_eq e d h])
    unfold b65e_tensorEval at ⊢ hi
    rw [eval₂_add, eval₂_mul, eval₂_C, coe_eval₂RingHom, eval₂_sub,
      b65e_velocityPolynomialQ_eval, b65e_velocityPolynomialQ_eval, hi]
    change _ + b65e_tensorEval (b65e_tensorDifferenceQ _) x y = _
    rw [b65e_tensorDifferenceQ_eval, b65e_dividedDifference_eq_div _ _ _ hxy,
      b65e_velocityPolynomialQ_eval, b65e_velocityPolynomialQ_eval]
    simp only [div_eq_mul_inv]
    ring

/-- The source-variable degree of each weight is below six. -/
theorem b65e_tensorWeightQ_natDegree (e d : Fin 2) :
    (b65e_tensorWeightQ e d).natDegree < 6 := by
  fin_cases e <;> fin_cases d <;>
    norm_num [b65e_tensorWeightQ, b65e_tensorInverseQ, b65e_otherFibre,
      b65e_tensorDifferenceQ, b65e_velocityPolynomialQ_natDegree,
      b65e_fibrePolynomialQ_natDegree, Finset.sum_range_succ] <;> compute_degree <;> norm_num

/-- No source reduction is needed for the pole weights. -/
theorem b65e_tensorWeightQ_reduce (e d : Fin 2) :
    b65e_tensorReduce d (b65e_tensorWeightQ e d) = b65e_tensorWeightQ e d := by
  apply (Polynomial.modByMonic_eq_self_iff ((b65e_fibrePolynomialQ_monic d).map
    (C : ℚ →+* ℚ[X]))).mpr
  apply Polynomial.degree_lt_degree
  rw [(b65e_fibrePolynomialQ_monic d).natDegree_map, b65e_fibrePolynomialQ_natDegree]
  exact b65e_tensorWeightQ_natDegree e d

/-- Polynomial weights of the moving-to-fixed pole ratio. -/
def b65e_fixedWeightQ (e : Fin 2) (k : Fin 4) : ℚ[X] :=
  b65e_velocityPolynomialQ e * b65e_fixedInverseQ e k

/-- Fixed-pole weights evaluate to the affine path ratio at the centre. -/
theorem b65e_fixedWeightQ_eval (e : Fin 2) (k : Fin 4) (x : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) :
    (b65e_fixedWeightQ e k).eval₂ (Rat.castHom ℂ) x =
      b65p_V (b65q_fibreValue e) x / (x - b65p_fixedPole k) := by
  rw [b65e_fixedWeightQ, eval₂_mul, b65e_velocityPolynomialQ_eval,
    b65e_fixedInverseQ_eval e k x hx, div_eq_mul_inv]

end HodgeLean.Foundations.Program
