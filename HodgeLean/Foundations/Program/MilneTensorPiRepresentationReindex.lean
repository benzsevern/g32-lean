import HodgeLean.Foundations.Program.MilneTensorPiRepresentation
import HodgeLean.Foundations.Program.MilneTensorRepresentationTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {I J : Type*} {R M : I → Type*}
    [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem m1b_piRepresentation_reindex_conj
    (ρ : (i : I) → R i →ₐ[ℂ] Module.End ℂ (M i)) (e : J ≃ I) (X : (i : I) → R i) :
    (LinearEquiv.piCongrLeft ℂ M e).symm.conj (m1b_piRepresentation ρ X) =
      m1b_piRepresentation (fun j : J => ρ (e j))
        ((AlgEquiv.piCongrLeft ℂ R e).symm X) := by
  let E := (LinearEquiv.piCongrLeft ℂ M e).symm
  have hnat (v : (i : I) → M i) :
      E (m1b_piRepresentation ρ X v) =
        m1b_piRepresentation (fun j : J => ρ (e j))
          ((AlgEquiv.piCongrLeft ℂ R e).symm X) (E v) := rfl
  apply LinearMap.ext
  intro w
  simpa only [LinearEquiv.conj_apply_apply, E.apply_symm_apply] using hnat (E.symm w)

end HodgeLean.Foundations.Program
