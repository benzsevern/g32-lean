import HodgeLean.Foundations.Program.MilneTensorDirectional
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.MvPolynomial.CommRing

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

def m1b_linePolynomial (x : σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (x i) * Polynomial.X)

theorem m1b_linePolynomial_derivative (x : σ → ℂ) (P : MvPolynomial σ ℂ) :
    (m1b_linePolynomial x P).derivative =
      m1b_linePolynomial x (m1b_directionalDerivative x P) := by
  have hC (c : ℂ) : m1b_linePolynomial x (MvPolynomial.C c) = Polynomial.C c :=
    (m1b_linePolynomial x).commutes c
  have hX (i : σ) : m1b_linePolynomial x (MvPolynomial.X i) =
      Polynomial.C (x i) * Polynomial.X := MvPolynomial.aeval_X _ _
  induction P using MvPolynomial.induction_on with
  | C c => simp only [hC, Polynomial.derivative_C, MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, Polynomial.derivative_mul, Derivation.leibniz,
      m1b_directionalDerivative_X, smul_eq_mul, map_add, hX, hC,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, one_mul,
      mul_one, add_zero, zero_add, hP]
    ring

theorem m1b_linePolynomial_iterate (n : ℕ) (x : σ → ℂ) (P : MvPolynomial σ ℂ) :
    Polynomial.derivative^[n] (m1b_linePolynomial x P) =
      m1b_linePolynomial x ((m1b_directionalDerivative x)^[n] P) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      m1b_linePolynomial_derivative, ih]

theorem m1b_linePolynomial_zero (x : σ → ℂ) (P : MvPolynomial σ ℂ) :
    (m1b_linePolynomial x P).eval 0 = MvPolynomial.eval (0 : σ → ℂ) P := by
  change Polynomial.evalRingHom 0
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (x i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  · ext c
    simp
  · funext i
    simp

end HodgeLean.Foundations.Program
