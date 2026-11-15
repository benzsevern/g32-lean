import HodgeLean.Foundations.Program.MilneTensorTotalOrbit
import HodgeLean.Foundations.Program.MilneTensorPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r n : ℕ}

theorem m1b_orbit_polynomial_on_form
    (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)))
    (Q : Matrix ι ι ℂ) (hQ : Q.toBilin' ∈ Set.range (m1b_formTransport B))
    (v : Fin n → Fin r → ι → ℂ) :
    MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2)
      (fun tc => v tc.1 tc.2.1 tc.2.2)) P = m1b_totalOrbitExtension B f Q.toBilin' v := by
  obtain ⟨e, he⟩ := hQ
  have hp := hP e v
  rw [he] at hp
  simp only [Matrix.toBilin'_single] at hp
  rw [← he, m1b_totalOrbitExtension_eval B f hf]
  exact hp

end HodgeLean.Foundations.Program
