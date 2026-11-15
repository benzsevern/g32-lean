import HodgeLean.Foundations.Program.MilneTensorDirectional
import Mathlib.Algebra.MvPolynomial.CommRing

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ τ : Type*}

theorem m1b_directional_substitution
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (x : σ → ℂ) (y : τ → ℂ)
    (hφ : ∀ i, m1b_directionalDerivative y (φ (MvPolynomial.X i)) = MvPolynomial.C (x i))
    (P : MvPolynomial σ ℂ) :
    m1b_directionalDerivative y (φ P) = φ (m1b_directionalDerivative x P) := by
  have hC (c : ℂ) : φ (MvPolynomial.C c) = MvPolynomial.C c := φ.commutes c
  induction P using MvPolynomial.induction_on with
  | C c => simp only [hC, MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, Derivation.leibniz, hφ, hP, m1b_directionalDerivative_X,
      smul_eq_mul, map_add, hC]

end HodgeLean.Foundations.Program
