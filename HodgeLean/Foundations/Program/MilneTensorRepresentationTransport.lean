import HodgeLean.Foundations.Program.MilneTensorNormOneAlgebraTransport
import HodgeLean.Foundations.Program.MilneTensorTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R S V W : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_representation_norm_one_conj_image
    (ρ : R →ₐ[ℂ] Module.End ℂ V) (ψ : S →ₐ[ℂ] Module.End ℂ W)
    (e : R ≃ₐ[ℂ] S) (E : V ≃ₗ[ℂ] W) (τ : R ≃ₗ[ℂ] R) (σ : S → S)
    (he : ∀ a, σ (e a) = e (τ a))
    (hE : ∀ a v, E (ρ a v) = ψ (e a) (E v)) :
    E.conj '' (ρ '' {a | τ a * a = 1}) = ψ '' {b | σ b * b = 1} := by
  have hconj (a) : E.conj (ρ a) = ψ (e a) := by
    apply LinearMap.ext
    intro w
    simpa only [LinearEquiv.conj_apply_apply, E.apply_symm_apply] using hE a (E.symm w)
  have hf : (fun a => E.conj (ρ a)) = (fun a => ψ (e a)) := funext hconj
  rw [Set.image_image, hf,
    ← Set.image_image, m1b_norm_one_algEquiv_image e τ σ he]

end HodgeLean.Foundations.Program
