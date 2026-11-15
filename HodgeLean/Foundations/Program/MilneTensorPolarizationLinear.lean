import HodgeLean.Foundations.Program.MilneTensorPolarization

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

def m1b_polarizationLinear (n : ℕ) : MvPolynomial σ ℂ →ₗ[ℂ]
    MultilinearMap ℂ (fun _ : Fin n => σ → ℂ) ℂ :=
  ((n.factorial : ℂ)⁻¹) •
    ((MvPolynomial.aeval (0 : σ → ℂ)).toLinearMap.compMultilinearMapₗ ℂ).comp
      (m1b_iteratedDirectional n)

theorem m1b_polarizationLinear_apply (n : ℕ) (P : MvPolynomial σ ℂ) :
    m1b_polarizationLinear n P = m1b_polarization n P := rfl

end HodgeLean.Foundations.Program
