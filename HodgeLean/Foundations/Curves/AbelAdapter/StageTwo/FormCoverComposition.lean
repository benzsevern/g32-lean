import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaForms

/-! # Constant covectors under a composite manifold map

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- An identity differential on a cover preserves the specified pulled-back constant covector.
Source: Griffiths–Harris, chapter 0 §2; formPullback_comp.
HC no distance; AV milestone no distance. -/
theorem formCoverComposition
    {V W S T : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [TopologicalSpace S] [ChartedSpace V S] [IsManifold 𝓘(ℂ, V) ω S]
    [TopologicalSpace T] [ChartedSpace W T] [IsManifold 𝓘(ℂ, W) ω T]
    (f : V → S) (hf : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, V) f)
    (hd : ∀ z, mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) f z = ContinuousLinearMap.id ℂ V)
    (g : S → T) (hg : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) g)
    (form : TangentBundle 𝓘(ℂ, W) T → ℂ) (ℓ : V →L[ℂ] ℂ)
    (hform : b3_pullback V W g form =
      (fun w : TangentBundle 𝓘(ℂ, V) S ↦ ℓ w.2)) :
    b3_pullback V W (g ∘ f) form =
      (fun w : TangentBundle 𝓘(ℂ, V) V ↦ ℓ w.2) := by
  rw [formPullback_comp f hf g hg, hform]
  funext w
  change ℓ (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) f w.1 w.2) = ℓ w.2
  rw [hd]
  rfl

#print axioms formCoverComposition
end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
