import HodgeLean.Foundations.Program.SchoenSelectedGeometryCenteredChart

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Centering and normalizing complex coordinates respects composition. -/
theorem s0_transport_comp (f g : ℂ → ℂ) (z₀ : ℂ) :
    b4cov_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ) (g ∘ f) z₀ =
      (b4cov_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ) g (f z₀)) ∘
        (b4cov_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ) f z₀) := by
  funext z
  simp only [b4cov_transport, Function.comp_apply, map_sub,
    ContinuousLinearEquiv.apply_symm_apply]
  congr 3
  abel

#print axioms s0_transport_comp
end HodgeLean.Foundations.Program
