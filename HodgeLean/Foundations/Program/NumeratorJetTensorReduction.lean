import HodgeLean.Foundations.Program.NumeratorJetMovingReduction
import Mathlib.Algebra.Polynomial.Bivariate

/-! # Reduction in both sextic variables -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Tensor evaluation is the two-variable algebra evaluation. -/
theorem b65e_tensorEval_eq_aevalAeval (g : ℚ[X][X]) (x y : ℂ) :
    b65e_tensorEval g x y = Polynomial.aevalAeval x y g := by
  have h : Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Rat.castHom ℂ) x) y =
      (Polynomial.aevalAeval (R := ℚ) x y).toRingHom := by
    ext <;> simp
  exact congrArg (fun f : ℚ[X][X] →+* ℂ ↦ f g) h

/-- Exchanging the two polynomial variables exchanges their evaluation points. -/
theorem b65e_tensorEval_swap (g : ℚ[X][X]) (x y : ℂ) :
    b65e_tensorEval (Polynomial.Bivariate.swap g) x y = b65e_tensorEval g y x := by
  simp only [b65e_tensorEval_eq_aevalAeval, Polynomial.Bivariate.aevalAeval_swap]

/-- Reduction in both the target and source sextic quotients. -/
def b65e_tensorReduceBoth (e d : Fin 2) (g : ℚ[X][X]) : ℚ[X][X] :=
  Polynomial.Bivariate.swap
    (b65e_tensorReduce e (Polynomial.Bivariate.swap (b65e_tensorReduce d g)))

/-- Two-variable reduction preserves evaluation on the two sextic fibres. -/
theorem b65e_tensorReduceBoth_eval (e d : Fin 2) (g : ℚ[X][X]) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) (hy : (b65q_fibreC d).eval y = 0) :
    b65e_tensorEval (b65e_tensorReduceBoth e d g) x y = b65e_tensorEval g x y := by
  rw [b65e_tensorReduceBoth, b65e_tensorEval_swap,
    b65e_tensorReduce_eval e _ y x hx, b65e_tensorEval_swap,
    b65e_tensorReduce_eval d _ x y hy]

/-- Geometric weights reduced in both sextic variables. -/
def b65e_reducedTensorRatioQ (e d : Fin 2) : ℕ → ℚ[X][X]
  | 0 => b65e_tensorReduceBoth e d (b65e_tensorWeightQ e d)
  | n + 1 => b65e_tensorReduceBoth e d
      (b65e_reducedTensorRatioQ e d n * (-b65e_tensorWeightQ e d))

/-- The reduced same-fibre and cross-fibre recurrences retain the geometric weights. -/
theorem b65e_reducedTensorRatioQ_eval (e d : Fin 2) (n : ℕ) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) (hy : (b65q_fibreC d).eval y = 0) :
    b65e_tensorEval (b65e_reducedTensorRatioQ e d n) x y =
      b65e_tensorEval (b65e_tensorRatioQ e d n) x y := by
  induction n with
  | zero =>
    rw [b65e_reducedTensorRatioQ, b65e_tensorReduceBoth_eval e d _ x y hx hy]
    simp only [b65e_tensorRatioQ, pow_zero, mul_one]
  | succ n ih =>
    rw [b65e_reducedTensorRatioQ, b65e_tensorReduceBoth_eval e d _ x y hx hy,
      b65e_tensorEval_mul, ih]
    unfold b65e_tensorRatioQ b65e_tensorEval
    simp only [eval₂_mul, eval₂_pow, eval₂_neg, pow_succ]
    ring

end HodgeLean.Foundations.Program
