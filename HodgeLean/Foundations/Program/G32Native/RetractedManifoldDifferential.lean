import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Retraction derivatives in the original manifold model

An identity on an ambient neighbourhood controls all model tangent directions.
-/

noncomputable section
open Filter Topology
open scoped Manifold
namespace HodgeLean.Foundations.TubularEuler

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem retraction_mfderiv_comp_of_interior
    (emb : M → F) (r : F → M) (C : Set M) (x : M)
    (hx : x ∈ interior C) (hfix : ∀ c ∈ C, r (emb c) = c)
    (hemb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) emb x)
    (hr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (emb x)) :
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (emb x)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) emb x) = ContinuousLinearMap.id ℝ E := by
  have heq : r ∘ emb =ᶠ[𝓝 x] id := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact hfix y hy
  rw [← mfderiv_comp x hr hemb, heq.mfderiv_eq]
  simp only [mfderiv_id, ContinuousLinearMap.comp_id]
  rfl

#print axioms retraction_mfderiv_comp_of_interior
end HodgeLean.Foundations.TubularEuler
