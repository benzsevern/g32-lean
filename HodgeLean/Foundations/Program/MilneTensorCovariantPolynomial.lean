import HodgeLean.Foundations.Program.MilneTensorPolynomialCovariance
import HodgeLean.Foundations.Program.MilneTensorOrbitReconstruction
import HodgeLean.Foundations.Program.MilneTensorProjectedOrbitFormula

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r n : ℕ}

theorem m1b_reconstructed_projected_orbit_polynomial
    (ε : ℂ) (hε : ε ^ 2 = 1)
    (C : Matrix ι ι ℂ) (hC : (m1b_matrixFormProjection ε C).det ≠ 0)
    (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (hB : ∀ x y, B y x = ε * B x y)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)))
    (horbit : ∀ Q : Matrix ι ι ℂ, Q.det ≠ 0 → Q.transpose = ε • Q →
      Q.toBilin' ∈ Set.range (m1b_formTransport B)) :
    ∃ R : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      (∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
        MvPolynomial.eval (Sum.elim
          (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
          (fun tc => v tc.1 tc.2.1 tc.2.2)) R = f (fun t c => e.symm (v t c))) ∧
      m1b_multilinearProjectionPolynomial R = R ∧
      ∀ M : Matrix ι ι ℂ, M.det ≠ 0 →
        m1b_linearSubstitution
          (m1b_sumCoordinateMap (m1b_congruenceCoordinates M) LinearMap.id) R =
        m1b_linearSubstitution
          (m1b_sumCoordinateMap LinearMap.id (m1b_repeatedVectorMap r n M)) R := by
  let P₁ := m1b_multilinearProjectionPolynomial P
  have hp₁ := m1b_orbit_polynomial_reconstruction B f P hP
  refine ⟨m1b_formProjectedPolynomial ε P₁, ?_, ?_, ?_⟩
  · exact m1b_formProjectedPolynomial_orbit ε hε B hB f P₁ hp₁
  · exact m1b_reconstruction_linearSubstitution_form (m1b_formProjectionCoordinates ε) P
  · intro M hM
    exact m1b_projected_orbit_polynomial_covariance ε hε C hC B f hf P₁ hp₁ horbit M hM

end HodgeLean.Foundations.Program
