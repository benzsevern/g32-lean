import HodgeLean.Foundations.AbelianQuotient.Defs

noncomputable section
namespace HodgeLean.Foundations.AbelianQuotient

/-- A linear map annihilating the kernel of a surjection factors through it. -/
theorem exists_linear_factor {V W T : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup T] [Module ℂ T]
    (Q : V →ₗ[ℂ] W) (hs : Function.Surjective Q) (F : V →ₗ[ℂ] T)
    (hker : ∀ v, Q v = 0 → F v = 0) : ∃ G : W →ₗ[ℂ] T, G.comp Q = F := by
  let Fbar := (LinearMap.ker Q).liftQ F (fun v hv => hker v hv)
  let e := Q.quotKerEquivOfSurjective hs
  refine ⟨Fbar.comp e.symm.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro v
  change Fbar (e.symm (Q v)) = F v
  rw [← show e (Submodule.Quotient.mk v) = Q v from rfl, e.symm_apply_apply]
  rfl

end HodgeLean.Foundations.AbelianQuotient
