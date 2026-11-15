import HodgeLean.Foundations.Program.MilneTensorOrbitProjection

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r n : ℕ}

theorem m1b_formProjectedPolynomial_orbit
    (ε : ℂ) (hε : ε ^ 2 = 1)
    (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (hB : ∀ x y, B y x = ε * B x y)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)))
    (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ) :
    MvPolynomial.eval (Sum.elim
      (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
      (fun tc => v tc.1 tc.2.1 tc.2.2)) (m1b_formProjectedPolynomial ε P) =
        f (fun t c => e.symm (v t c)) := by
  let Q : Matrix ι ι ℂ := fun i j => m1b_formTransport B e (Pi.single i 1) (Pi.single j 1)
  change MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2)
    (fun tc => v tc.1 tc.2.1 tc.2.2)) (m1b_formProjectedPolynomial ε P) = _
  rw [m1b_formProjectedPolynomial_eval,
    m1b_matrixFormProjection_fixed ε hε Q (m1b_formTransport_matrix_sign ε B hB e)]
  exact hP e v

end HodgeLean.Foundations.Program
