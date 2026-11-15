import HodgeLean.Foundations.Program.MilneTensorNormOneTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]

def m1b_transportInvolution (e : R ≃ₐ[ℂ] S) (τ : R ≃ₗ[ℂ] R) : S ≃ₗ[ℂ] S :=
  (e.symm.toLinearEquiv.trans τ).trans e.toLinearEquiv

theorem m1b_transportInvolution_properties (e : R ≃ₐ[ℂ] S) (τ : R ≃ₗ[ℂ] R)
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a) :
    Function.Involutive (m1b_transportInvolution e τ) ∧
      ∀ a b, m1b_transportInvolution e τ (a * b) =
        m1b_transportInvolution e τ b * m1b_transportInvolution e τ a := by
  constructor
  · intro x
    change e (τ (e.symm (e (τ (e.symm x))))) = x
    rw [e.symm_apply_apply, hτ, e.apply_symm_apply]
  · intro a b
    change e (τ (e.symm (a * b))) = e (τ (e.symm b)) * e (τ (e.symm a))
    rw [map_mul, hmul, map_mul]

end HodgeLean.Foundations.Program
