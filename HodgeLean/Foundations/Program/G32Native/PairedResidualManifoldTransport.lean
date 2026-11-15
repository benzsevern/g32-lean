import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! # Transporting differential rank through an original analytic equivalence -/
noncomputable section
set_option maxHeartbeats 200000
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- A differentiable homeomorphism with differentiable inverse preserves
surjectivity of the differential of the original map.
Source: Mathlib, Geometry.Manifold.MFDeriv.Basic, mfderiv_comp. -/
theorem residual_mfderiv_surjective_of_homeomorph_comp
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {M N P : Type} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    [IsManifold 𝓘(ℂ, E) 1 M] [IsManifold 𝓘(ℂ, F) 1 N]
    [IsManifold 𝓘(ℂ, G) 1 P]
    (T : P ≃ₜ N) (f : M → N) (x : M)
    (hT : MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, F) T)
    (hTi : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, G) T.symm)
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x)
    (hs : Function.Surjective
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (T.symm ∘ f) x)) :
    Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x) := by
  have hid : T ∘ T.symm = id := funext T.apply_symm_apply
  have hc := mfderiv_comp (f x) (hT (T.symm (f x))) (hTi (f x))
  rw [hid, mfderiv_id] at hc
  have hTs : Function.Surjective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) T (T.symm (f x))) := by
    intro v
    refine ⟨mfderiv 𝓘(ℂ, F) 𝓘(ℂ, G) T.symm (f x) v, ?_⟩
    exact (congrArg (fun A => A v) hc).symm
  have he : T ∘ (T.symm ∘ f) = f := funext (fun w => T.apply_symm_apply _)
  have hd := mfderiv_comp x (hT (T.symm (f x))) ((hTi (f x)).comp x hf)
  rw [he] at hd
  intro v
  obtain ⟨u, hu⟩ := hTs v
  obtain ⟨w, hw⟩ := hs u
  refine ⟨w, ?_⟩
  rw [hd]
  exact (congrArg (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) T (T.symm (f x))) hw).trans hu

#print axioms residual_mfderiv_surjective_of_homeomorph_comp
end HodgeLean.Foundations.Program.G32Native
