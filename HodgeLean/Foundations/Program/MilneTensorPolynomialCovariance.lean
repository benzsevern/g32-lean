import HodgeLean.Foundations.Program.MilneTensorProjectedPolynomial
import HodgeLean.Foundations.Program.MilneTensorProjectedDensity
import HodgeLean.Foundations.Program.MilneTensorOrbitPolynomialForm
import HodgeLean.Foundations.Program.MilneTensorOrbitCongruence

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r n : ℕ}

theorem m1b_projected_orbit_polynomial_covariance
    (ε : ℂ) (hε : ε ^ 2 = 1)
    (C : Matrix ι ι ℂ) (hC : (m1b_matrixFormProjection ε C).det ≠ 0)
    (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)))
    (horbit : ∀ Q : Matrix ι ι ℂ, Q.det ≠ 0 → Q.transpose = ε • Q →
      Q.toBilin' ∈ Set.range (m1b_formTransport B))
    (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    m1b_linearSubstitution
      (m1b_sumCoordinateMap (m1b_congruenceCoordinates M) LinearMap.id)
      (m1b_formProjectedPolynomial ε P) =
    m1b_linearSubstitution
      (m1b_sumCoordinateMap LinearMap.id (m1b_repeatedVectorMap r n M))
      (m1b_formProjectedPolynomial ε P) := by
  apply m1b_projected_polynomial_identity ε C hC
  intro Q v hQ
  rw [m1b_linearSubstitution_eval, m1b_linearSubstitution_eval]
  change MvPolynomial.eval
      (Sum.elim (fun ij : ι × ι => (M.transpose * Q * M) ij.1 ij.2) v)
      (m1b_formProjectedPolynomial ε P) =
    MvPolynomial.eval (Sum.elim (fun ij : ι × ι => Q ij.1 ij.2)
      (fun tc : Fin n × (Fin r × ι) => (M *ᵥ (fun i => v (tc.1, tc.2.1, i))) tc.2.2))
      (m1b_formProjectedPolynomial ε P)
  rw [m1b_formProjectedPolynomial_eval, m1b_formProjectedPolynomial_eval,
    m1b_matrixFormProjection_congruence]
  let R := m1b_matrixFormProjection ε Q
  let w : Fin n → Fin r → ι → ℂ := fun t c i => v (t, c, i)
  have hR : R.toBilin' ∈ Set.range (m1b_formTransport B) :=
    horbit R hQ (m1b_matrixFormProjection_transpose ε hε Q)
  have hMR := m1b_congruence_mem_orbit B M R hM hR
  exact (m1b_orbit_polynomial_on_form B f hf P hP _ hMR w).trans
    ((m1b_totalOrbitExtension_congruence B f hf M R hM w).trans
      (m1b_orbit_polynomial_on_form B f hf P hP R hR (fun t c => M *ᵥ w t c)).symm)

end HodgeLean.Foundations.Program
