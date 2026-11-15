import HodgeLean.Foundations.Program.MilneTensorPolarizationSubstitution

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ τ : Type*} [Fintype τ] [DecidableEq τ]

def m1b_linearSubstitution (L : (τ → ℂ) →ₗ[ℂ] (σ → ℂ)) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ :=
  MvPolynomial.aeval (fun i => ∑ j,
    MvPolynomial.C (L (Pi.single j 1) i) * MvPolynomial.X j)

theorem m1b_linear_coordinate_expansion (L : (τ → ℂ) →ₗ[ℂ] (σ → ℂ))
    (x : τ → ℂ) (i : σ) :
    L x i = ∑ j, x j * L (Pi.single j 1) i := by
  have hx : x = ∑ j, x j • Pi.single j (1 : ℂ) := by
    ext j
    simp [Pi.single_apply, apply_ite]
  conv_lhs => rw [hx, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem m1b_linearSubstitution_eval (L : (τ → ℂ) →ₗ[ℂ] (σ → ℂ))
    (P : MvPolynomial σ ℂ) (x : τ → ℂ) :
    MvPolynomial.eval x (m1b_linearSubstitution L P) = MvPolynomial.eval (L x) P := by
  have hX (i : σ) : MvPolynomial.eval x
      (m1b_linearSubstitution L (MvPolynomial.X i)) = L x i := by
    simp only [m1b_linearSubstitution, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, m1b_linear_coordinate_expansion L x i]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hC (c : ℂ) : m1b_linearSubstitution L (MvPolynomial.C c) = MvPolynomial.C c :=
    (m1b_linearSubstitution L).commutes c
  induction P using MvPolynomial.induction_on with
  | C c => simp only [hC, MvPolynomial.eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, hP, hX, MvPolynomial.eval_X]

theorem m1b_linearSubstitution_directional (L : (τ → ℂ) →ₗ[ℂ] (σ → ℂ))
    (x : τ → ℂ) (i : σ) :
    m1b_directionalDerivative x (m1b_linearSubstitution L (MvPolynomial.X i)) =
      MvPolynomial.C (L x i) := by
  simp only [m1b_linearSubstitution, MvPolynomial.aeval_X, map_sum,
    Derivation.leibniz, MvPolynomial.derivation_C, m1b_directionalDerivative_X,
    smul_eq_mul, mul_zero, add_zero]
  rw [m1b_linear_coordinate_expansion L x i, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, mul_comm]

theorem m1b_polarization_linearSubstitution (n : ℕ)
    (L : (τ → ℂ) →ₗ[ℂ] (σ → ℂ)) (P : MvPolynomial σ ℂ) (v : Fin n → τ → ℂ) :
    m1b_polarization n (m1b_linearSubstitution L P) v =
      m1b_polarization n P (fun t => L (v t)) := by
  apply m1b_polarization_substitution n (m1b_linearSubstitution L) L
    (m1b_linearSubstitution_directional L)
  intro i
  rw [m1b_linearSubstitution_eval, map_zero, MvPolynomial.eval_X]
  rfl

end HodgeLean.Foundations.Program
