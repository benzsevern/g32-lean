import HodgeLean.Foundations.Program.MilneTensorWeightedCoefficient

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

theorem m1b_weighted_substitution_eval (w : σ → ℕ)
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (c : ℂ) :
    ((MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (x i) * Polynomial.X ^ w i)) P).eval c =
        MvPolynomial.eval (fun i => x i * c ^ w i) P := by
  change Polynomial.evalRingHom c _ = _
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  · ext z
    simp
  · funext i
    simp

theorem m1b_weightedCoefficient_recovery (w : σ → ℕ) (n : ℕ)
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (z : ℂ)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval (fun i => x i * c ^ w i) P = c ^ n * z) :
    MvPolynomial.eval x (m1b_weightedCoefficient w n P) = z := by
  let q := (MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) * Polynomial.X ^ w i)) P
  have hq : q * Polynomial.X = (Polynomial.C z * Polynomial.X ^ n) * Polynomial.X := by
    apply Polynomial.funext
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X]
      change q.eval c * c = _
      rw [show q.eval c = c ^ n * z from
        (m1b_weighted_substitution_eval w P x c).trans (h c hc)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      ring
  have heq : q = Polynomial.C z * Polynomial.X ^ n :=
    mul_right_cancel₀ Polynomial.X_ne_zero hq
  rw [m1b_weightedCoefficient_eval]
  change q.coeff n = z
  rw [heq]
  simp

end HodgeLean.Foundations.Program
