import HodgeLean.Foundations.Program.MilneTensorJointPolarization
import HodgeLean.Foundations.Program.MilneTensorOrbitScalar
import HodgeLean.Foundations.Program.MilneTensorPolarizationRecovery

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r k : ℕ}

theorem m1b_jointPolarization_orbit_diagonal
    (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin (k * 2) => Fin r → ι → ℂ) ℂ)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin (k * 2) × (Fin r × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin (k * 2) → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)))
    (hrec : m1b_multilinearProjectionPolynomial P = P)
    (v : Fin (k * 2) → Fin r → ι → ℂ) :
    m1b_jointPolarization k P (fun t ci => v t ci.1 ci.2)
      (fun _ ij => B (Pi.single ij.1 1) (Pi.single ij.2 1)) = f v := by
  rw [m1b_jointPolarization_apply, hrec]
  apply m1b_polarization_square_scaling
  intro c hc
  rw [m1b_formPolynomialAt_eval]
  have h := m1b_orbit_polynomial_scalar B f P hP (LinearEquiv.refl ℂ _) v c hc
  have he : c ^ (k * 2) = c ^ (2 * k) := congrArg (fun n => c ^ n) (Nat.mul_comm k 2)
  rw [he] at h
  exact h

end HodgeLean.Foundations.Program
