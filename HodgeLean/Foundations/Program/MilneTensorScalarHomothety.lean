import HodgeLean.Foundations.Program.MilneTensorOrbit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_formTransport_scalar (B : LinearMap.BilinForm ℂ V)
    (e : V ≃ₗ[ℂ] V) (a : ℂˣ) :
    m1b_formTransport B (e.trans (LinearEquiv.smulOfUnit a⁻¹)) =
      (a.val ^ 2) • m1b_formTransport B e := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change B (e.symm (a.val • x)) (e.symm (a.val • y)) =
    a.val ^ 2 * B (e.symm x) (e.symm y)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

end HodgeLean.Foundations.Program
