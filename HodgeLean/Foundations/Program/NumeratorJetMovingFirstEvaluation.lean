import HodgeLean.Foundations.Program.NumeratorJetMovingFirstCertificates

/-! # First moving coefficients of the analytic Schlesinger solution -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- The four trace calculations assembled over both fibre indices. -/
theorem b65e_movingTrace_certificate (e d : Fin 2) (z : ℂ) :
    (b65e_partialTraceQ d (b65e_tensorWeightQ e d)).eval₂ (Rat.castHom ℂ) z =
      (b65e_movingTraceQ e d).eval₂ (Rat.castHom ℂ) z := by
  fin_cases e <;> fin_cases d
  · exact b65e_movingTrace_certificate_0_0 z
  · exact b65e_movingTrace_certificate_0_1 z
  · exact b65e_movingTrace_certificate_1_0 z
  · exact b65e_movingTrace_certificate_1_1 z

/-- The four trace reductions assembled over both fibre indices. -/
theorem b65e_movingTrace_reduction (e d : Fin 2) :
    b65e_movingTraceQ e d = b65e_reducedMovingTraceQ e d +
      b65e_fibrePolynomialQ e * b65e_movingTraceQuotQ e d := by
  fin_cases e <;> fin_cases d
  · exact b65e_movingTrace_reduction_0_0
  · exact b65e_movingTrace_reduction_0_1
  · exact b65e_movingTrace_reduction_1_0
  · exact b65e_movingTrace_reduction_1_1

/-- A reduced trace has the original trace value on the target fibre. -/
theorem b65e_reducedMovingTrace_eval (e d : Fin 2) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    (b65e_reducedMovingTraceQ e d).eval₂ (Rat.castHom ℂ) z =
      (b65e_partialTraceQ d (b65e_tensorWeightQ e d)).eval₂ (Rat.castHom ℂ) z := by
  have hroot : (b65e_fibrePolynomialQ e).eval₂ (Rat.castHom ℂ) z = 0 := by
    rwa [← eval_map, b65e_fibrePolynomialQ_map]
  rw [b65e_movingTrace_certificate, b65e_movingTrace_reduction,
    eval₂_add, eval₂_mul, hroot,
    zero_mul, add_zero]

/-- The polynomial field at the centre evaluates to the stored first moving coefficient. -/
theorem b65e_movingFirstPolynomialQ_eval (e : Fin 2) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) (i j : Fin 4) :
    (b65e_movingFirstPolynomialQ e i j).eval₂ (Rat.castHom ℂ) z =
      ∑ c : Fin 6, (b65e_movingJet 1 e c i j : ℂ) * z ^ (c : ℕ) := by
  have hw (k : Fin 4) :
      (b65e_fixedWeightQ e k).eval₂ (Rat.castHom ℂ) z =
        (b65e_reducedFixedWeightQ 0 e k).eval₂ (Rat.castHom ℂ) z := by
    simpa only [b65e_fixedRatioQ, b65e_fixedWeightQ, pow_zero, mul_one] using
      (b65e_fixedWeight_zero_eval e k z hz).symm
  simp only [b65e_movingFirstPolynomialQ, eval₂_add, eval₂_finsetSum,
    eval₂_mul, eval₂_C, Rat.coe_castHom, hw,
    ← b65e_reducedMovingTrace_eval e _ z hz]
  simp only [b65e_reducedFixedWeightQ, b65e_ofFn_eq_sum,
    b65e_reducedMovingTraceQ, eval₂_finsetSum, eval₂_mul, eval₂_C,
    eval₂_pow, eval₂_X, Rat.coe_castHom, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← b65e_movingFirst_table]
  unfold b65e_movingFirstCoeffQ
  push_cast
  simp only [Finset.sum_mul, add_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring

/-- The first coefficient of any analytic moving-residue series is the stored coefficient. -/
theorem b65e_moving_residue_coeff_one (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (x : Fin 12) (i j : Fin 4) {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt (fun θ ↦ b65q_res O.residue θ (Sum.inr x) i j) P 0) :
    P.coeff 1 = b65e_residueJet p 1 (.inr x) i j := by
  have h := hP.hasDerivAt.unique
    (b65e_residue_hasDerivAt p O (Sum.inr x) i j (Metric.mem_ball_self O.radius_pos))
  change P.coeff 1 = b65e_fieldEntry p O.residue 0 (Sum.inr x) i j at h
  rw [h, b65e_fieldEntry_moving_zero p O x i j,
    b65e_movingFirstPolynomialQ_eval]
  · simp only [b65e_residueJet, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, Rat.coe_castHom, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · exact b65q_fibre_root O _ (by
      simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and])

end HodgeLean.Foundations.Program
