import HodgeLean.Foundations.Program.MilneTensorProjectedPolynomial
import HodgeLean.Foundations.Program.MilneTensorOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [DecidableEq ι]

theorem m1b_formTransport_matrix_sign (ε : ℂ)
    (B : LinearMap.BilinForm ℂ (ι → ℂ)) (hB : ∀ x y, B y x = ε * B x y)
    (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) :
    Matrix.transpose (fun i j => m1b_formTransport B e (Pi.single i 1) (Pi.single j 1)) =
      ε • (fun i j => m1b_formTransport B e (Pi.single i 1) (Pi.single j 1)) := by
  ext i j
  exact hB (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1))

end HodgeLean.Foundations.Program
