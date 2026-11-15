import HodgeLean.Foundations.Program.MilneTensorPolarization
import HodgeLean.Foundations.Program.MilneTensorDirectionalSubstitution

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ τ : Type*}

theorem m1b_iteratedDirectional_substitution (n : ℕ)
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (L : (τ → ℂ) →ₗ[ℂ] (σ → ℂ))
    (hφ : ∀ y i, m1b_directionalDerivative y (φ (MvPolynomial.X i)) =
      MvPolynomial.C (L y i))
    (P : MvPolynomial σ ℂ) (v : Fin n → τ → ℂ) :
    m1b_iteratedDirectional n (φ P) v =
      φ (m1b_iteratedDirectional n P (fun t => L (v t))) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [m1b_iteratedDirectional_succ, m1b_iteratedDirectional_succ,
      m1b_directional_substitution φ (L (v 0)) (v 0) (hφ (v 0)), ih]

theorem m1b_substitution_zero
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (hφ : ∀ i, MvPolynomial.eval (0 : τ → ℂ) (φ (MvPolynomial.X i)) = 0)
    (P : MvPolynomial σ ℂ) :
    MvPolynomial.eval (0 : τ → ℂ) (φ P) = MvPolynomial.eval (0 : σ → ℂ) P := by
  have hC (c : ℂ) : φ (MvPolynomial.C c) = MvPolynomial.C c := φ.commutes c
  induction P using MvPolynomial.induction_on with
  | C c => simp only [hC, MvPolynomial.eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, hφ, MvPolynomial.eval_X, Pi.zero_apply, mul_zero]

theorem m1b_polarization_substitution (n : ℕ)
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (L : (τ → ℂ) →ₗ[ℂ] (σ → ℂ))
    (hφ : ∀ y i, m1b_directionalDerivative y (φ (MvPolynomial.X i)) =
      MvPolynomial.C (L y i))
    (hzero : ∀ i, MvPolynomial.eval (0 : τ → ℂ) (φ (MvPolynomial.X i)) = 0)
    (P : MvPolynomial σ ℂ) (v : Fin n → τ → ℂ) :
    m1b_polarization n (φ P) v = m1b_polarization n P (fun t => L (v t)) := by
  change (n.factorial : ℂ)⁻¹ * MvPolynomial.eval (0 : τ → ℂ)
    (m1b_iteratedDirectional n (φ P) v) =
      (n.factorial : ℂ)⁻¹ * MvPolynomial.eval (0 : σ → ℂ)
        (m1b_iteratedDirectional n P (fun t => L (v t)))
  rw [m1b_iteratedDirectional_substitution n φ L hφ, m1b_substitution_zero φ hzero]

end HodgeLean.Foundations.Program
