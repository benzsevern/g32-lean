import HodgeLean.Foundations.Program.MilneTensorPolarization
import HodgeLean.Foundations.Program.MilneTensorWeightedRecovery
import HodgeLean.Foundations.Program.MilneTensorOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

theorem m1b_polarization_square_scaling (k : ℕ) (P : MvPolynomial σ ℂ)
    (x : σ → ℂ) (z : ℂ)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval (fun i => x i * c ^ 2) P = c ^ (2 * k) * z) :
    m1b_polarization k P (fun _ => x) = z := by
  have hlin (c : ℂ) (hc : c ≠ 0) :
      MvPolynomial.eval (fun i => x i * c ^ (1 : ℕ)) P = c ^ k * z := by
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by decide)
    have hs0 : s ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by decide)] at hs
      exact hc hs.symm
    have hh := h s hs0
    rw [pow_mul, hs] at hh
    simpa only [pow_one, hs] using hh
  have hr := m1b_weightedCoefficient_recovery (fun _ : σ => 1) k P x z hlin
  rw [m1b_weightedCoefficient_eval] at hr
  rw [m1b_polarization_diagonal]
  change ((MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) * Polynomial.X)) P).coeff k = z
  simpa only [pow_one] using hr

end HodgeLean.Foundations.Program
