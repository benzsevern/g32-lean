import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! # Surjective derivatives transferred from analytic compositions -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- A composite with surjective derivative forces surjectivity of its outer
map's derivative at the actual intermediate point.
Source: Lang, Real and Functional Analysis, ch. XIII, chain rule. -/
theorem residual_surjective_fderiv_of_composition
    {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (g : F → G) (T : E → F) (x : E)
    (hg : DifferentiableAt 𝕜 g (T x)) (hT : DifferentiableAt 𝕜 T x)
    (h : Function.Surjective (fderiv 𝕜 (g ∘ T) x)) :
    Function.Surjective (fderiv 𝕜 g (T x)) := by
  intro y
  obtain ⟨v, hv⟩ := h y
  refine ⟨fderiv 𝕜 T x v, ?_⟩
  have he := congrArg (fun A => A v) (fderiv_comp x hg hT)
  exact he.symm.trans hv

#print axioms residual_surjective_fderiv_of_composition
end HodgeLean.Foundations.Program.G32Native
