import HodgeLean.Foundations.Program.MilneTensorNormOneAlgebraTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R S V : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]
    [AddCommGroup V] [Module ℂ V]

theorem m1b_norm_one_representation_algEquiv_image
    (ρ : R →ₐ[ℂ] Module.End ℂ V) (e : R ≃ₐ[ℂ] S) (τ : R ≃ₗ[ℂ] R) (σ : S → S)
    (he : ∀ a, σ (e a) = e (τ a)) :
    ρ '' {a | τ a * a = 1} = (ρ.comp e.symm.toAlgHom) '' {b | σ b * b = 1} := by
  rw [← m1b_norm_one_algEquiv_image e τ σ he, Set.image_image]
  congr 1
  funext a
  change ρ a = ρ (e.symm (e a))
  rw [e.symm_apply_apply]

end HodgeLean.Foundations.Program
