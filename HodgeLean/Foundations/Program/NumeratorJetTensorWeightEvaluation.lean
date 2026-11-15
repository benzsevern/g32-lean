import HodgeLean.Foundations.Program.NumeratorJetTensorWeightCertificates
import HodgeLean.Foundations.Program.NumeratorJetTensorCoordinateEvaluation
import HodgeLean.Foundations.Program.NumeratorJetMovingWeights

/-! # Evaluation of the certified rational geometric tensor weights -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- The initial certified tensor array evaluates to the original rational weight. -/
theorem b65e_tensorWeightCoeffQ_zero_eval (e d : Fin 2) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) :
    b65e_tensorCoordinateEvalQ (b65e_tensorWeightCoeffQ 0 e d) x y =
      b65e_tensorEval (b65e_tensorWeightQ e d) x y := by
  have hc : b65e_initialTensorCoordsQ e d = b65e_tensorWeightCoeffQ 0 e d := by
    funext c h
    exact b65e_tensorWeight_certificate_zero e d c h
  rw [← hc]
  exact b65e_initialTensorCoordsQ_eval e d x y hx

/-- All seven certified tensor arrays have the value of the geometric denominator series. -/
theorem b65e_tensorWeightCoeffQ_eval (n : Fin 7) (e d : Fin 2) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) (hy : (b65q_fibreC d).eval y = 0) :
    b65e_tensorCoordinateEvalQ (b65e_tensorWeightCoeffQ n e d) x y =
      b65e_tensorEval (b65e_tensorRatioQ e d n) x y := by
  obtain ⟨n, hn⟩ := n
  induction n with
  | zero =>
    change b65e_tensorCoordinateEvalQ (b65e_tensorWeightCoeffQ 0 e d) x y =
      b65e_tensorEval (b65e_tensorRatioQ e d 0) x y
    rw [b65e_tensorWeightCoeffQ_zero_eval e d x y hx]
    simp only [b65e_tensorRatioQ, pow_zero, mul_one]
  | succ n ih =>
    have hc : b65e_tensorCoordinateMulQ e d
        (b65e_tensorWeightCoeffQ (⟨n, by omega⟩ : Fin 7) e d)
        (fun a b ↦ -b65e_tensorWeightCoeffQ 0 e d a b) =
          b65e_tensorWeightCoeffQ (⟨n + 1, hn⟩ : Fin 7) e d := by
      funext c h
      exact b65e_tensorWeight_certificate_succ ⟨n, by omega⟩ e d c h
    rw [← hc, b65e_tensorCoordinateMulQ_eval e d _ _ x y hx hy,
      b65e_tensorCoordinateEvalQ_neg, ih (by omega),
      b65e_tensorWeightCoeffQ_zero_eval e d x y hx]
    unfold b65e_tensorRatioQ b65e_tensorEval
    simp only [eval₂_mul, eval₂_pow, eval₂_neg, pow_succ]
    ring

/-- On distinct labelled moving poles, the certified arrays evaluate to the actual pole ratios. -/
theorem b65e_tensorWeightCoeffQ_poleRatioCoeff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 7) (x y : Fin 12) (hxy : x ≠ y) :
    b65e_tensorCoordinateEvalQ
        (b65e_tensorWeightCoeffQ n (b65q_fibreIndex x) (b65q_fibreIndex y)) (p x) (p y) =
      b65e_poleRatioCoeff p (.inr x) (.inr y) n := by
  rw [b65e_tensorWeightCoeffQ_eval n _ _ (p x) (p y)
    (b65q_fibre_root O _ (by
      simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]))
    (b65q_fibre_root O _ (by
      simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]))]
  exact b65e_tensorRatioQ_eval p O x y hxy n

end HodgeLean.Foundations.Program
