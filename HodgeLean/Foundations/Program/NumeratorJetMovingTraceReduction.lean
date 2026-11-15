import HodgeLean.Foundations.Program.NumeratorJetMovingTrace
import HodgeLean.Foundations.Program.NumeratorJetFixedWeightEvaluation

/-! # Reduced initial moving-weight traces -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- A sextic reduction identity follows from sixteen rational coefficient checks. -/
theorem b65e_polynomial_reduction_certificate (u : Fin 16 → ℚ) (r : Fin 6 → ℚ)
    (e : Fin 2) (q : Fin 10 → ℚ)
    (h : ∀ n : Fin 16,
      b65e_vectorCoeffQ u n.val = b65e_vectorCoeffQ r n.val +
        ∑ a ∈ Finset.range (n.val + 1),
          b65e_vectorCoeffQ (b65q_fibreCoeff e) a * b65e_vectorCoeffQ q (n.val - a)) :
    Polynomial.ofFn 16 u = Polynomial.ofFn 6 r +
      b65e_fibrePolynomialQ e * Polynomial.ofFn 10 q := by
  have h16 : (Polynomial.ofFn 16 u).natDegree ≤ 15 := by
    have := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ 16) u
    omega
  have h6 : (Polynomial.ofFn 6 r).natDegree ≤ 5 := by
    have := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ 6) r
    omega
  have h10 : (Polynomial.ofFn 10 q).natDegree ≤ 9 := by
    have := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ 10) q
    omega
  have hr : (Polynomial.ofFn 6 r + b65e_fibrePolynomialQ e *
      Polynomial.ofFn 10 q).natDegree ≤ 15 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · omega
    · exact natDegree_mul_le_of_le (le_of_eq (b65e_fibrePolynomialQ_natDegree e)) h10
  have hf : b65e_fibrePolynomialQ e = Polynomial.ofFn 7 (b65q_fibreCoeff e) := by
    rw [b65e_ofFn_eq_sum]
    rfl
  apply (Polynomial.ext_iff_natDegree_le (n := 15) h16 hr).2
  intro n hn
  rw [coeff_add, b65e_cross_mul_coeff, hf]
  simp only [b65e_ofFn_coeff]
  exact h ⟨n, by omega⟩

/-- Reduced traces of the initial moving weights. -/
def b65e_reducedMovingTraceCoeffQ : Fin 2 → Fin 2 → Fin 6 → ℚ :=
  ![![![(-5256903/1792), (148977/448), (-3879/112), (153/28), (-18/7), 0], ![(-74049/56000), (-7247/3500), (442651/140000), (-190923/70000), (191207/140000), (17753/35000)]],
    ![![(-18759033/6400), (3719777/11200), (-33953/800), (18147/2800), (2171/5600), (331/700)], ![(-2493/448), (-27/56), (18/7), 0, 0, 0]]]

/-- Quotients witnessing the reduction of the four trace polynomials. -/
def b65e_movingTraceQuotCoeffQ : Fin 2 → Fin 2 → Fin 10 → ℚ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![(39419/87500), (10459/21875), (-231439/700000), (-64751/700000), (6201/100000), (-40881/140000), (63141/140000), (-2733/35000), (-1701/100000), (-297/8750)]],
    ![![(521/1250), (9113/43750), (104827/350000), (-123181/350000), (-53811/350000), (123729/350000), (-129837/350000), (8313/17500), (-61641/350000), (-297/8750)], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Reduced trace polynomial. -/
def b65e_reducedMovingTraceQ (e d : Fin 2) : ℚ[X] :=
  ∑ c : Fin 6, C (b65e_reducedMovingTraceCoeffQ e d c) * X ^ (c : ℕ)

/-- Polynomial quotient for each trace reduction. -/
def b65e_movingTraceQuotQ (e d : Fin 2) : ℚ[X] :=
  ∑ c : Fin 10, C (b65e_movingTraceQuotCoeffQ e d c) * X ^ (c : ℕ)

set_option maxHeartbeats 400000 in
/-- Trace reduction for target fibre 0 and source fibre 0. -/
theorem b65e_movingTrace_reduction_0_0 :
    b65e_movingTraceQ 0 0 = b65e_reducedMovingTraceQ 0 0 +
      b65e_fibrePolynomialQ 0 * b65e_movingTraceQuotQ 0 0 := by
  have h := b65e_polynomial_reduction_certificate
    (b65e_movingTraceCoeffQ 0 0) (b65e_reducedMovingTraceCoeffQ 0 0) 0
    (b65e_movingTraceQuotCoeffQ 0 0) (by decide +kernel)
  simpa only [b65e_ofFn_eq_sum, b65e_movingTraceQ,
    b65e_reducedMovingTraceQ, b65e_movingTraceQuotQ] using h

set_option maxHeartbeats 400000 in
/-- Trace reduction for target fibre 0 and source fibre 1. -/
theorem b65e_movingTrace_reduction_0_1 :
    b65e_movingTraceQ 0 1 = b65e_reducedMovingTraceQ 0 1 +
      b65e_fibrePolynomialQ 0 * b65e_movingTraceQuotQ 0 1 := by
  have h := b65e_polynomial_reduction_certificate
    (b65e_movingTraceCoeffQ 0 1) (b65e_reducedMovingTraceCoeffQ 0 1) 0
    (b65e_movingTraceQuotCoeffQ 0 1) (by decide +kernel)
  simpa only [b65e_ofFn_eq_sum, b65e_movingTraceQ,
    b65e_reducedMovingTraceQ, b65e_movingTraceQuotQ] using h

set_option maxHeartbeats 400000 in
/-- Trace reduction for target fibre 1 and source fibre 0. -/
theorem b65e_movingTrace_reduction_1_0 :
    b65e_movingTraceQ 1 0 = b65e_reducedMovingTraceQ 1 0 +
      b65e_fibrePolynomialQ 1 * b65e_movingTraceQuotQ 1 0 := by
  have h := b65e_polynomial_reduction_certificate
    (b65e_movingTraceCoeffQ 1 0) (b65e_reducedMovingTraceCoeffQ 1 0) 1
    (b65e_movingTraceQuotCoeffQ 1 0) (by decide +kernel)
  simpa only [b65e_ofFn_eq_sum, b65e_movingTraceQ,
    b65e_reducedMovingTraceQ, b65e_movingTraceQuotQ] using h

set_option maxHeartbeats 400000 in
/-- Trace reduction for target fibre 1 and source fibre 1. -/
theorem b65e_movingTrace_reduction_1_1 :
    b65e_movingTraceQ 1 1 = b65e_reducedMovingTraceQ 1 1 +
      b65e_fibrePolynomialQ 1 * b65e_movingTraceQuotQ 1 1 := by
  have h := b65e_polynomial_reduction_certificate
    (b65e_movingTraceCoeffQ 1 1) (b65e_reducedMovingTraceCoeffQ 1 1) 1
    (b65e_movingTraceQuotCoeffQ 1 1) (by decide +kernel)
  simpa only [b65e_ofFn_eq_sum, b65e_movingTraceQ,
    b65e_reducedMovingTraceQ, b65e_movingTraceQuotQ] using h

end HodgeLean.Foundations.Program
