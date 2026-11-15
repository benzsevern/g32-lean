import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Complex.Basic

/-! # Localizing an analytic parameter to a specified open chart domain -/

noncomputable section
open Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem localize_manifold_parameter
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace F M]
    (σ : E → M) (b : E) (S : Set M) (hS : IsOpen S) (hb : σ b ∈ S)
    (hσ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ω σ b) :
    ∃ τ : E → M, ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ω τ b ∧
      (∀ c, τ c ∈ S) ∧ τ =ᶠ[𝓝 b] σ ∧ τ b = σ b := by
  classical
  let τ := fun c => if σ c ∈ S then σ c else σ b
  have heq : τ =ᶠ[𝓝 b] σ := by
    filter_upwards [hσ.continuousAt.eventually (hS.mem_nhds hb)] with c hc
    exact if_pos hc
  refine ⟨τ, hσ.congr_of_eventuallyEq heq, ?_, heq, if_pos hb⟩
  intro c
  dsimp only [τ]
  by_cases hc : σ c ∈ S
  · rw [if_pos hc]
    exact hc
  · rw [if_neg hc]
    exact hb

#print axioms localize_manifold_parameter
end HodgeLean.Foundations.TubularEuler
