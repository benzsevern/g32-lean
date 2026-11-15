import HodgeLean.Foundations.Program.NumeratorJetMovingFirst

/-! # Initial moving-weight traces in rational coordinates -/

noncomputable section
open Polynomial Fin.NatCast
namespace HodgeLean.Foundations.Program

set_option maxRecDepth 8192

/-- Trace of the six source coefficients before source reduction. -/
def b65e_tensorTraceSixQ (d : Fin 2) (g : ℚ[X][X]) : ℚ[X] :=
  ∑ j : Fin 6, g.coeff j * C (b65q_psumQ d j)

/-- The six-coefficient trace preserves addition. -/
theorem b65e_tensorTraceSixQ_add (d : Fin 2) (f g : ℚ[X][X]) :
    b65e_tensorTraceSixQ d (f + g) =
      b65e_tensorTraceSixQ d f + b65e_tensorTraceSixQ d g := by
  simp only [b65e_tensorTraceSixQ, coeff_add, add_mul, Finset.sum_add_distrib]

/-- Target-polynomial factors can be taken outside the source trace. -/
theorem b65e_tensorTraceSixQ_C_mul (d : Fin 2) (a : ℚ[X]) (g : ℚ[X][X]) :
    b65e_tensorTraceSixQ d (C a * g) = a * b65e_tensorTraceSixQ d g := by
  simp only [b65e_tensorTraceSixQ, coeff_C_mul, Finset.mul_sum, mul_assoc]

/-- The traced divided difference, with source moments substituted. -/
def b65e_differenceTraceQ (d : Fin 2) (g : ℚ[X]) : ℚ[X] :=
  ∑ n ∈ Finset.range (g.natDegree + 1), C (g.coeff n) *
    ∑ i ∈ Finset.range n, X ^ i * C (b65q_psumQ d (Fin.ofNat 6 (n - 1 - i)))

set_option maxHeartbeats 400000 in
/-- Divided differences of degree at most six use just the six source moments. -/
theorem b65e_tensorTraceSixQ_difference (d : Fin 2) (g : ℚ[X])
    (hg : g.natDegree ≤ 6) :
    b65e_tensorTraceSixQ d (b65e_tensorDifferenceQ g) = b65e_differenceTraceQ d g := by
  have h1 : ((1 : ℕ) : Fin 6) = 1 := by decide +kernel
  generalize hk : g.natDegree = k at *
  interval_cases k <;> fin_cases d <;>
    norm_num [b65q_psumQ, b65e_tensorTraceSixQ, b65e_tensorDifferenceQ, b65e_differenceTraceQ,
      hk, Fin.sum_univ_succ, Finset.sum_range_succ, coeff_C_mul,
      coeff_mul_X_pow, coeff_C, coeff_X, Fin.ofNat_eq_cast, h1, ← map_pow] <;> ring

/-- Source traces of the four initial moving weights, in ascending powers. -/
def b65e_movingTraceCoeffQ : Fin 2 → Fin 2 → Fin 16 → ℚ :=
  ![![![(-5256903/1792), (148977/448), (-3879/112), (153/28), (-18/7), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![(-1631653/280000), (-33/350), (5527227/700000), (-4822163/700000), (1197073/560000), (-5671037/1400000), (-854157/560000), (1193273/100000), (-4425857/350000), (6954587/560000), (-176253/16000), (3014661/700000), (-650697/2800000), (1099311/2800000), (-172287/700000), (-297/8750)]],
    ![![(-469442641/160000), (469057773/1400000), (-3594237/100000), (565357/100000), (-289681/400000), (-20475227/1400000), (39116307/2800000), (302317/350000), (-209713/25000), (42570571/2800000), (-42939411/2800000), (953139/175000), (621291/2800000), (54753/400000), (-37503/175000), (-297/8750)], ![(-2493/448), (-27/56), (18/7), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Polynomial encoding of the initial moving-weight traces. -/
def b65e_movingTraceQ (e d : Fin 2) : ℚ[X] :=
  ∑ c : Fin 16, C (b65e_movingTraceCoeffQ e d c) * X ^ (c : ℕ)

set_option maxHeartbeats 400000 in
/-- Initial weight trace for target fibre 0 and source fibre 0. -/
theorem b65e_movingTrace_certificate_0_0 (z : ℂ) :
    (b65e_partialTraceQ 0 (b65e_tensorWeightQ 0 0)).eval₂ (Rat.castHom ℂ) z =
      (b65e_movingTraceQ 0 0).eval₂ (Rat.castHom ℂ) z := by
  change (b65e_tensorTraceSixQ _ (b65e_tensorReduce _ _)).eval₂ (Rat.castHom ℂ) z = _
  rw [b65e_tensorWeightQ_reduce]
  unfold b65e_tensorWeightQ
  rw [ite_eq_left rfl]
  rw [b65e_tensorTraceSixQ_difference 0 (b65e_velocityPolynomialQ 0) (by
    rw [b65e_velocityPolynomialQ_natDegree]; norm_num)]
  simp only [b65e_differenceTraceQ, b65e_velocityPolynomialQ_natDegree,
    b65e_fibrePolynomialQ_natDegree]
  norm_num [b65e_velocityPolynomialQ, b65e_velocityQ,
    b65e_fibrePolynomialQ, b65q_fibreCoeff, b65e_otherFibre,
    b65e_crossInverseQ, b65e_crossInverseCoeffQ, b65q_psumQ,
    b65e_movingTraceQ, b65e_movingTraceCoeffQ,
    Fin.sum_univ_succ, Finset.sum_range_succ, coeff_C_mul_X_pow, coeff_X,
    Fin.ofNat_eq_cast, eval₂_add, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X, eval₂_pow, eval₂_finsetSum, Rat.coe_castHom]
  ring

set_option maxHeartbeats 400000 in
/-- Initial weight trace for target fibre 0 and source fibre 1. -/
theorem b65e_movingTrace_certificate_0_1 (z : ℂ) :
    (b65e_partialTraceQ 1 (b65e_tensorWeightQ 0 1)).eval₂ (Rat.castHom ℂ) z =
      (b65e_movingTraceQ 0 1).eval₂ (Rat.castHom ℂ) z := by
  change (b65e_tensorTraceSixQ _ (b65e_tensorReduce _ _)).eval₂ (Rat.castHom ℂ) z = _
  rw [b65e_tensorWeightQ_reduce]
  unfold b65e_tensorWeightQ
  rw [ite_eq_right (by decide)]
  simp only [b65e_tensorInverseQ, b65e_tensorTraceSixQ_add,
    b65e_tensorTraceSixQ_C_mul]
  rw [b65e_tensorTraceSixQ_difference 1
    (b65e_fibrePolynomialQ (b65e_otherFibre 0)) (by
      rw [b65e_fibrePolynomialQ_natDegree]),
    b65e_tensorTraceSixQ_difference 1 (b65e_velocityPolynomialQ 1) (by
      rw [b65e_velocityPolynomialQ_natDegree]; norm_num)]
  simp only [b65e_differenceTraceQ, b65e_velocityPolynomialQ_natDegree,
    b65e_fibrePolynomialQ_natDegree]
  norm_num [b65e_velocityPolynomialQ, b65e_velocityQ,
    b65e_fibrePolynomialQ, b65q_fibreCoeff, b65e_otherFibre,
    b65e_crossInverseQ, b65e_crossInverseCoeffQ, b65q_psumQ,
    b65e_movingTraceQ, b65e_movingTraceCoeffQ,
    Fin.sum_univ_succ, Finset.sum_range_succ, coeff_C_mul_X_pow, coeff_X,
    Fin.ofNat_eq_cast, eval₂_add, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X, eval₂_pow, eval₂_finsetSum, Rat.coe_castHom]
  ring

set_option maxHeartbeats 400000 in
/-- Initial weight trace for target fibre 1 and source fibre 0. -/
theorem b65e_movingTrace_certificate_1_0 (z : ℂ) :
    (b65e_partialTraceQ 0 (b65e_tensorWeightQ 1 0)).eval₂ (Rat.castHom ℂ) z =
      (b65e_movingTraceQ 1 0).eval₂ (Rat.castHom ℂ) z := by
  change (b65e_tensorTraceSixQ _ (b65e_tensorReduce _ _)).eval₂ (Rat.castHom ℂ) z = _
  rw [b65e_tensorWeightQ_reduce]
  unfold b65e_tensorWeightQ
  rw [ite_eq_right (by decide)]
  simp only [b65e_tensorInverseQ, b65e_tensorTraceSixQ_add,
    b65e_tensorTraceSixQ_C_mul]
  rw [b65e_tensorTraceSixQ_difference 0
    (b65e_fibrePolynomialQ (b65e_otherFibre 1)) (by
      rw [b65e_fibrePolynomialQ_natDegree]),
    b65e_tensorTraceSixQ_difference 0 (b65e_velocityPolynomialQ 0) (by
      rw [b65e_velocityPolynomialQ_natDegree]; norm_num)]
  simp only [b65e_differenceTraceQ, b65e_velocityPolynomialQ_natDegree,
    b65e_fibrePolynomialQ_natDegree]
  norm_num [b65e_velocityPolynomialQ, b65e_velocityQ,
    b65e_fibrePolynomialQ, b65q_fibreCoeff, b65e_otherFibre,
    b65e_crossInverseQ, b65e_crossInverseCoeffQ, b65q_psumQ,
    b65e_movingTraceQ, b65e_movingTraceCoeffQ,
    Fin.sum_univ_succ, Finset.sum_range_succ, coeff_C_mul_X_pow, coeff_X,
    Fin.ofNat_eq_cast, eval₂_add, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X, eval₂_pow, eval₂_finsetSum, Rat.coe_castHom]
  ring

set_option maxHeartbeats 400000 in
/-- Initial weight trace for target fibre 1 and source fibre 1. -/
theorem b65e_movingTrace_certificate_1_1 (z : ℂ) :
    (b65e_partialTraceQ 1 (b65e_tensorWeightQ 1 1)).eval₂ (Rat.castHom ℂ) z =
      (b65e_movingTraceQ 1 1).eval₂ (Rat.castHom ℂ) z := by
  change (b65e_tensorTraceSixQ _ (b65e_tensorReduce _ _)).eval₂ (Rat.castHom ℂ) z = _
  rw [b65e_tensorWeightQ_reduce]
  unfold b65e_tensorWeightQ
  rw [ite_eq_left rfl]
  rw [b65e_tensorTraceSixQ_difference 1 (b65e_velocityPolynomialQ 1) (by
    rw [b65e_velocityPolynomialQ_natDegree]; norm_num)]
  simp only [b65e_differenceTraceQ, b65e_velocityPolynomialQ_natDegree,
    b65e_fibrePolynomialQ_natDegree]
  norm_num [b65e_velocityPolynomialQ, b65e_velocityQ,
    b65e_fibrePolynomialQ, b65q_fibreCoeff, b65e_otherFibre,
    b65e_crossInverseQ, b65e_crossInverseCoeffQ, b65q_psumQ,
    b65e_movingTraceQ, b65e_movingTraceCoeffQ,
    Fin.sum_univ_succ, Finset.sum_range_succ, coeff_C_mul_X_pow, coeff_X,
    Fin.ofNat_eq_cast, eval₂_add, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X, eval₂_pow, eval₂_finsetSum, Rat.coe_castHom]
  ring

end HodgeLean.Foundations.Program
