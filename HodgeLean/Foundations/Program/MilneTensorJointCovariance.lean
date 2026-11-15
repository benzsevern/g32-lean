import HodgeLean.Foundations.Program.MilneTensorJointPolarization
import HodgeLean.Foundations.Program.MilneTensorPartialCovariance

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  {n : ℕ}

theorem m1b_jointPolarization_covariance (k : ℕ)
    (L : (σ → ℂ) →ₗ[ℂ] (σ → ℂ))
    (N : (Fin n × ι → ℂ) →ₗ[ℂ] (Fin n × ι → ℂ))
    (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ)
    (hrec : m1b_multilinearProjectionPolynomial P = P)
    (hP : m1b_linearSubstitution (m1b_sumCoordinateMap L LinearMap.id) P =
      m1b_linearSubstitution (m1b_sumCoordinateMap LinearMap.id N) P)
    (v : Fin n → ι → ℂ) (q : Fin k → σ → ℂ) :
    m1b_jointPolarization k P v (fun t => L (q t)) =
      m1b_jointPolarization k P (fun t i => N (fun ti => v ti.1 ti.2) (t, i)) q := by
  rw [m1b_jointPolarization_apply, m1b_jointPolarization_apply, hrec]
  exact m1b_partial_polarization_covariance k L N P hP (fun ti => v ti.1 ti.2) q

end HodgeLean.Foundations.Program
