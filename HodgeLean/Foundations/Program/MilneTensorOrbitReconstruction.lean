import HodgeLean.Foundations.Program.MilneTensorOrbit
import HodgeLean.Foundations.Program.MilneTensorReconstruction
import HodgeLean.Foundations.Program.MilneTensorDiagonal

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r n : ℕ}

theorem m1b_orbit_polynomial_reconstruction
    (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)))
    (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ) :
    MvPolynomial.eval (Sum.elim
      (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
      (fun tc => v tc.1 tc.2.1 tc.2.2)) (m1b_multilinearProjectionPolynomial P) =
        f (fun t c => e.symm (v t c)) := by
  let g := f.compLinearMap (fun _ =>
    (m1b_copiesEquiv e r).symm.toLinearMap.comp (m1b_copyCoordinates (ι := ι) r))
  change MvPolynomial.eval (Sum.elim
      (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
      (fun tc => v tc.1 tc.2.1 tc.2.2)) (m1b_multilinearProjectionPolynomial P) =
    g (fun t ci => v t ci.1 ci.2)
  refine m1b_multilinearProjectionPolynomial_eval P _ g ?_ (fun t ci => v t ci.1 ci.2)
  intro a
  exact hP e (fun t c i => (Pi.single (a t) 1 : (Fin r × ι) → ℂ) (c, i))

end HodgeLean.Foundations.Program
