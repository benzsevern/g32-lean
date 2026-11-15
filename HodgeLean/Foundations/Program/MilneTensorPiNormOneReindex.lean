import HodgeLean.Foundations.Program.MilneTensorPiRepresentationReindex

noncomputable section
namespace HodgeLean.Foundations.Program
variable {I J : Type*} {R M : I → Type*}
    [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem m1b_pi_norm_one_reindex_image
    (ρ : (i : I) → R i →ₐ[ℂ] Module.End ℂ (M i)) (e : J ≃ I)
    (τ : ((i : I) → R i) ≃ₗ[ℂ] ((i : I) → R i))
    (σ : ((j : J) → R (e j)) → ((j : J) → R (e j)))
    (he : ∀ X, σ ((AlgEquiv.piCongrLeft ℂ R e).symm X) =
      (AlgEquiv.piCongrLeft ℂ R e).symm (τ X)) :
    (LinearEquiv.piCongrLeft ℂ M e).symm.conj ''
      (m1b_piRepresentation ρ '' {X | τ X * X = 1}) =
      m1b_piRepresentation (fun j : J => ρ (e j)) '' {X | σ X * X = 1} :=
  m1b_representation_norm_one_conj_image _ _ (AlgEquiv.piCongrLeft ℂ R e).symm
    (LinearEquiv.piCongrLeft ℂ M e).symm τ σ he (fun _ _ => rfl)

theorem m1b_pi_norm_one_reindex_generation
    (ρ : (i : I) → R i →ₐ[ℂ] Module.End ℂ (M i)) (e : J ≃ I)
    (τ : ((i : I) → R i) ≃ₗ[ℂ] ((i : I) → R i))
    (σ : ((j : J) → R (e j)) → ((j : J) → R (e j)))
    (he : ∀ X, σ ((AlgEquiv.piCongrLeft ℂ R e).symm X) =
      (AlgEquiv.piCongrLeft ℂ R e).symm (τ X)) (n : ℕ)
    (hgen : m1b_fixed (m1b_piRepresentation (fun j : J => ρ (e j)) '' {X | σ X * X = 1}) n =
      m1b_products (m1b_fixed
        (m1b_piRepresentation (fun j : J => ρ (e j)) '' {X | σ X * X = 1}) 2) n) :
    m1b_fixed (m1b_piRepresentation ρ '' {X | τ X * X = 1}) n =
      m1b_products (m1b_fixed (m1b_piRepresentation ρ '' {X | τ X * X = 1}) 2) n := by
  apply (m1b_generation_conj_iff (LinearEquiv.piCongrLeft ℂ M e).symm _ n).mpr
  rw [m1b_pi_norm_one_reindex_image ρ e τ σ he]
  exact hgen

end HodgeLean.Foundations.Program
