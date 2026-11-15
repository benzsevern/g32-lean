import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaForms

/-! # Transport of holomorphic forms along analytic homeomorphisms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E F S T : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace S] [ChartedSpace E S] [IsManifold 𝓘(ℂ, E) ω S]
  [TopologicalSpace T] [ChartedSpace F T] [IsManifold 𝓘(ℂ, F) ω T]

/-- Transport of forms with the literal tangent normalization along an analytic homeomorphism.
Source: Griffiths–Harris, chapter 0 §2; formPullback_inverse.
HC no distance; AV milestone no distance. -/
def analyticFormTransport (f : S ≃ₜ T)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hg : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ω f.symm) :
    b3_HolForm E S ≃ₗ[ℂ] b3_HolForm F T where
  toFun θ := ⟨b3_pullback F E f.symm θ.val,
    b3_pullback_mem_holForm f.symm hg θ.val θ.2⟩
  invFun θ := ⟨b3_pullback E F f θ.val,
    b3_pullback_mem_holForm f hf θ.val θ.2⟩
  left_inv θ := Subtype.ext (formPullback_inverse f
    (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)) θ.val)
  right_inv θ := Subtype.ext (formPullback_inverse f.symm
    (hg.mdifferentiable (by simp)) (hf.mdifferentiable (by simp)) θ.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The transported form evaluates by the actual derivative of the inverse map.
Source: Griffiths–Harris, chapter 0 §2; b3_pullback.
HC no distance; AV milestone no distance. -/
theorem analyticFormTransport_apply (f : S ≃ₜ T)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hg : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ω f.symm) (θ : b3_HolForm E S) :
    (analyticFormTransport f hf hg θ).val = b3_pullback F E f.symm θ.val := rfl

#print axioms analyticFormTransport
#print axioms analyticFormTransport_apply

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
