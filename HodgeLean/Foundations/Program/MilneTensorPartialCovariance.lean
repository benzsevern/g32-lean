import Mathlib.Algebra.CharZero.Infinite
import HodgeLean.Foundations.Program.MilneTensorPartialPolynomial
import HodgeLean.Foundations.Program.MilneTensorCovarianceCoordinates
import Mathlib.Algebra.MvPolynomial.Funext

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ζ : Type*} [Fintype σ] [DecidableEq σ] [Fintype ζ] [DecidableEq ζ]

theorem m1b_formPolynomialAt_covariance
    (L : (σ → ℂ) →ₗ[ℂ] (σ → ℂ)) (N : (ζ → ℂ) →ₗ[ℂ] (ζ → ℂ))
    (P : MvPolynomial (σ ⊕ ζ) ℂ)
    (hP : m1b_linearSubstitution (m1b_sumCoordinateMap L LinearMap.id) P =
      m1b_linearSubstitution (m1b_sumCoordinateMap LinearMap.id N) P)
    (v : ζ → ℂ) :
    m1b_linearSubstitution L (m1b_formPolynomialAt P v) =
      m1b_formPolynomialAt P (N v) := by
  apply MvPolynomial.funext
  intro x
  rw [m1b_linearSubstitution_eval, m1b_formPolynomialAt_eval, m1b_formPolynomialAt_eval]
  have h := congrArg (MvPolynomial.eval (Sum.elim x v)) hP
  rw [m1b_linearSubstitution_eval, m1b_linearSubstitution_eval] at h
  exact h

theorem m1b_partial_polarization_covariance (k : ℕ)
    (L : (σ → ℂ) →ₗ[ℂ] (σ → ℂ)) (N : (ζ → ℂ) →ₗ[ℂ] (ζ → ℂ))
    (P : MvPolynomial (σ ⊕ ζ) ℂ)
    (hP : m1b_linearSubstitution (m1b_sumCoordinateMap L LinearMap.id) P =
      m1b_linearSubstitution (m1b_sumCoordinateMap LinearMap.id N) P)
    (v : ζ → ℂ) (q : Fin k → σ → ℂ) :
    m1b_polarization k (m1b_formPolynomialAt P v) (fun t => L (q t)) =
      m1b_polarization k (m1b_formPolynomialAt P (N v)) q := by
  have h := congrArg (fun R => m1b_polarization k R q)
    (m1b_formPolynomialAt_covariance L N P hP v)
  rw [m1b_polarization_linearSubstitution] at h
  exact h

end HodgeLean.Foundations.Program
