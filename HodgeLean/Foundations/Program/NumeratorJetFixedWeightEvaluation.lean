import HodgeLean.Foundations.Program.NumeratorJetFixedWeights

/-! # Evaluation of reduced weights on the labelled sextic roots -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- All eight initial weight identities. -/
theorem b65e_fixedWeight_certificate_zero (e : Fin 2) (k : Fin 4) :
    b65e_velocityPolynomialQ e * b65e_fixedInverseQ e k =
      b65e_reducedFixedWeightQ 0 e k + b65e_fibrePolynomialQ e * b65e_fixedWeightQuotQ 0 e k := by
  fin_cases e <;> fin_cases k
  · exact b65e_fixedWeight_certificate_0_0_0
  · exact b65e_fixedWeight_certificate_0_0_1
  · exact b65e_fixedWeight_certificate_0_0_2
  · exact b65e_fixedWeight_certificate_0_0_3
  · exact b65e_fixedWeight_certificate_0_1_0
  · exact b65e_fixedWeight_certificate_0_1_1
  · exact b65e_fixedWeight_certificate_0_1_2
  · exact b65e_fixedWeight_certificate_0_1_3

/-- All forty-eight positive-order weight recurrence identities. -/
theorem b65e_fixedWeight_certificate_succ (n : Fin 6) (e : Fin 2) (k : Fin 4) :
    -(b65e_reducedFixedWeightQ 0 e k) * b65e_reducedFixedWeightQ n.castSucc e k =
      b65e_reducedFixedWeightQ n.succ e k +
        b65e_fibrePolynomialQ e * b65e_fixedWeightQuotQ n.succ e k := by
  fin_cases n <;> fin_cases e <;> fin_cases k
  · exact b65e_fixedWeight_certificate_1_0_0
  · exact b65e_fixedWeight_certificate_1_0_1
  · exact b65e_fixedWeight_certificate_1_0_2
  · exact b65e_fixedWeight_certificate_1_0_3
  · exact b65e_fixedWeight_certificate_1_1_0
  · exact b65e_fixedWeight_certificate_1_1_1
  · exact b65e_fixedWeight_certificate_1_1_2
  · exact b65e_fixedWeight_certificate_1_1_3
  · exact b65e_fixedWeight_certificate_2_0_0
  · exact b65e_fixedWeight_certificate_2_0_1
  · exact b65e_fixedWeight_certificate_2_0_2
  · exact b65e_fixedWeight_certificate_2_0_3
  · exact b65e_fixedWeight_certificate_2_1_0
  · exact b65e_fixedWeight_certificate_2_1_1
  · exact b65e_fixedWeight_certificate_2_1_2
  · exact b65e_fixedWeight_certificate_2_1_3
  · exact b65e_fixedWeight_certificate_3_0_0
  · exact b65e_fixedWeight_certificate_3_0_1
  · exact b65e_fixedWeight_certificate_3_0_2
  · exact b65e_fixedWeight_certificate_3_0_3
  · exact b65e_fixedWeight_certificate_3_1_0
  · exact b65e_fixedWeight_certificate_3_1_1
  · exact b65e_fixedWeight_certificate_3_1_2
  · exact b65e_fixedWeight_certificate_3_1_3
  · exact b65e_fixedWeight_certificate_4_0_0
  · exact b65e_fixedWeight_certificate_4_0_1
  · exact b65e_fixedWeight_certificate_4_0_2
  · exact b65e_fixedWeight_certificate_4_0_3
  · exact b65e_fixedWeight_certificate_4_1_0
  · exact b65e_fixedWeight_certificate_4_1_1
  · exact b65e_fixedWeight_certificate_4_1_2
  · exact b65e_fixedWeight_certificate_4_1_3
  · exact b65e_fixedWeight_certificate_5_0_0
  · exact b65e_fixedWeight_certificate_5_0_1
  · exact b65e_fixedWeight_certificate_5_0_2
  · exact b65e_fixedWeight_certificate_5_0_3
  · exact b65e_fixedWeight_certificate_5_1_0
  · exact b65e_fixedWeight_certificate_5_1_1
  · exact b65e_fixedWeight_certificate_5_1_2
  · exact b65e_fixedWeight_certificate_5_1_3
  · exact b65e_fixedWeight_certificate_6_0_0
  · exact b65e_fixedWeight_certificate_6_0_1
  · exact b65e_fixedWeight_certificate_6_0_2
  · exact b65e_fixedWeight_certificate_6_0_3
  · exact b65e_fixedWeight_certificate_6_1_0
  · exact b65e_fixedWeight_certificate_6_1_1
  · exact b65e_fixedWeight_certificate_6_1_2
  · exact b65e_fixedWeight_certificate_6_1_3

/-- The unreduced geometric weights satisfy a multiplication recurrence. -/
theorem b65e_fixedRatioQ_succ (e : Fin 2) (k : Fin 4) (n : ℕ) :
    b65e_fixedRatioQ e k (n + 1) =
      -(b65e_fixedRatioQ e k 0) * b65e_fixedRatioQ e k n := by
  simp only [b65e_fixedRatioQ, pow_zero, mul_one, pow_succ]
  ring

/-- Reduction of the initial weight preserves its value on a sextic root. -/
theorem b65e_fixedWeight_zero_eval (e : Fin 2) (k : Fin 4) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    (b65e_reducedFixedWeightQ 0 e k).eval₂ (Rat.castHom ℂ) z =
      (b65e_fixedRatioQ e k 0).eval₂ (Rat.castHom ℂ) z := by
  have hroot : (b65e_fibrePolynomialQ e).eval₂ (Rat.castHom ℂ) z = 0 := by
    rwa [← Polynomial.eval_map, b65e_fibrePolynomialQ_map]
  have h := congrArg (fun g : ℚ[X] ↦ g.eval₂ (Rat.castHom ℂ) z)
    (b65e_fixedWeight_certificate_zero e k)
  simpa only [b65e_fixedRatioQ, pow_zero, mul_one, eval₂_mul, eval₂_add,
    hroot, zero_mul, add_zero] using h.symm

/-- Every reduced weight through order six has the value of its geometric coefficient. -/
theorem b65e_fixedWeight_eval (e : Fin 2) (k : Fin 4) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) (n : Fin 7) :
    (b65e_reducedFixedWeightQ n e k).eval₂ (Rat.castHom ℂ) z =
      (b65e_fixedRatioQ e k n).eval₂ (Rat.castHom ℂ) z := by
  have hroot : (b65e_fibrePolynomialQ e).eval₂ (Rat.castHom ℂ) z = 0 := by
    rwa [← Polynomial.eval_map, b65e_fibrePolynomialQ_map]
  obtain ⟨n, hn⟩ := n
  induction n with
  | zero => exact b65e_fixedWeight_zero_eval e k z hz
  | succ n ih =>
    have h := congrArg (fun g : ℚ[X] ↦ g.eval₂ (Rat.castHom ℂ) z)
      (b65e_fixedWeight_certificate_succ ⟨n, by omega⟩ e k)
    simp only [eval₂_mul, eval₂_add, eval₂_neg, hroot, zero_mul, add_zero] at h
    rw [b65e_fixedRatioQ_succ, eval₂_mul, eval₂_neg,
      ← b65e_fixedWeight_zero_eval e k z hz, ← ih (by omega)]
    exact h.symm

/-- The reduced rational weights give the actual fixed-to-moving pole coefficients. -/
theorem b65e_fixedWeight_poleRatioCoeff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e : Fin 2) (k : Fin 4) (x : Fin 12) (hx : x ∈ b65q_fibreSet e) (n : Fin 7) :
    (b65e_reducedFixedWeightQ n e k).eval₂ (Rat.castHom ℂ) (p x) =
      b65e_poleRatioCoeff p (.inl k) (.inr x) n := by
  rw [b65e_fixedWeight_eval e k (p x) (b65q_fibre_root O e hx)]
  exact b65e_fixedRatioQ_eval p O e k x hx n

end HodgeLean.Foundations.Program
