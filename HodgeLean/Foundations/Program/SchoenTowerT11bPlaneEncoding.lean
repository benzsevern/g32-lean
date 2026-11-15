import HodgeLean.Foundations.Program.SchoenTowerT11bPlaneAlgebraicTriviality
import HodgeLean.Foundations.Program.SchoenTowerT11bGraph
import Mathlib.Algebra.MvPolynomial.Funext

/-! Bivariate polynomial encoding retaining the last coordinate as parameter.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Regard a plane polynomial as a polynomial in the first coordinate with parameter-polynomial coefficients.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, coordinate encoding step. -/
def s2v_t11b_planeFamilyPolynomial :
    MvPolynomial (Fin 2) ℝ →+* Polynomial (Polynomial ℝ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun i => if i = 0 then Polynomial.X else Polynomial.C Polynomial.X)

/-- The plane encoding evaluates at the original spatial and last coordinates.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, coordinate encoding step. -/
theorem s2v_t11b_eval_planeFamilyPolynomial (p : MvPolynomial (Fin 2) ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (s2v_t11b_planeFamilyPolynomial p).eval₂ (Polynomial.evalRingHom (y 1)) (y 0) =
      MvPolynomial.eval (fun i => y i) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [s2v_t11b_planeFamilyPolynomial, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, Polynomial.eval₂_C, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq =>
    simp only [map_add, Polynomial.eval₂_add, MvPolynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    congr 1
    fin_cases i <;>
      simp [s2v_t11b_planeFamilyPolynomial]

/-- The plane family encoding loses no polynomial information.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, coordinate encoding step. -/
theorem s2v_t11b_planeFamilyPolynomial_injective :
    Function.Injective s2v_t11b_planeFamilyPolynomial := by
  intro p q h
  apply MvPolynomial.funext
  intro z
  let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 z
  have hp := s2v_t11b_eval_planeFamilyPolynomial p y
  have hq := s2v_t11b_eval_planeFamilyPolynomial q y
  exact hp.symm.trans ((congrArg
    (fun P : Polynomial (Polynomial ℝ) => P.eval₂ (Polynomial.evalRingHom (y 1)) (y 0)) h).trans hq)

end HodgeLean.Foundations.Program
