import HodgeLean.Foundations.Program.NumeratorJetQuotient

/-! # Polynomial divided differences for moving-pole interactions -/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The polynomial divided difference, also defined on the diagonal. -/
def b65e_dividedDifference (g : ℚ[X]) (x y : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (g.natDegree + 1), (g.coeff n : ℂ) *
    ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)

/-- Multiplying a divided difference by the displacement gives the value difference. -/
theorem b65e_dividedDifference_mul (g : ℚ[X]) (x y : ℂ) :
    b65e_dividedDifference g x y * (x - y) =
      g.eval₂ (Rat.castHom ℂ) x - g.eval₂ (Rat.castHom ℂ) y := by
  unfold b65e_dividedDifference
  rw [Finset.sum_mul, eval₂_eq_sum_range, eval₂_eq_sum_range, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_assoc, geom_sum₂_mul]
  simp only [Rat.coe_castHom]
  ring

/-- Away from the diagonal the polynomial expression is the usual quotient. -/
theorem b65e_dividedDifference_eq_div (g : ℚ[X]) (x y : ℂ) (hxy : x ≠ y) :
    b65e_dividedDifference g x y =
      (g.eval₂ (Rat.castHom ℂ) x - g.eval₂ (Rat.castHom ℂ) y) / (x - y) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).mpr
  exact b65e_dividedDifference_mul g x y

/-- Rational polynomials with the two velocity coefficient arrays. -/
def b65e_velocityPolynomialQ (e : Fin 2) : ℚ[X] :=
  ∑ i : Fin 6, C (b65e_velocityQ e i) * X ^ (i : ℕ)

/-- Polynomial evaluation gives the path velocity on either fibre. -/
theorem b65e_velocityPolynomialQ_eval (e : Fin 2) (z : ℂ) :
    (b65e_velocityPolynomialQ e).eval₂ (Rat.castHom ℂ) z =
      b65p_V (b65q_fibreValue e) z := by
  rw [b65e_velocityQ_eval]
  simp only [b65e_velocityPolynomialQ, eval₂_finsetSum, eval₂_mul, eval₂_C,
    eval₂_pow, eval₂_X, Rat.coe_castHom]

/-- The same-fibre pole ratio at the base is a polynomial divided difference. -/
theorem b65e_sameFibre_ratio (e : Fin 2) (x y : ℂ) (hxy : x ≠ y) :
    (b65p_V (b65q_fibreValue e) x - b65p_V (b65q_fibreValue e) y) / (x - y) =
      b65e_dividedDifference (b65e_velocityPolynomialQ e) x y := by
  rw [b65e_dividedDifference_eq_div _ _ _ hxy,
    b65e_velocityPolynomialQ_eval, b65e_velocityPolynomialQ_eval]

end HodgeLean.Foundations.Program
