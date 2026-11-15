import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import HodgeLean.Foundations.Program.G32Native.SelfChartDerivatives

/-! # Restricting regularity in the original complex manifold charts

The complex and real self models use the same chart functions and topology.
-/

open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem contMDiffAt_real_of_complex
    {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    {n : ℕ∞ω} {f : M → N} {x : M}
    (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) n f x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) n f x := by
  rw [contMDiffAt_iff] at hf ⊢
  refine ⟨hf.1, ?_⟩
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id]
    using hf.2.restrict_scalars ℝ

#print axioms contMDiffAt_real_of_complex

theorem hasMFDerivAt_real_of_complex
    {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    {f : M → N} {x : M} {A : E →L[ℂ] F}
    (hf : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x A) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x (A.restrictScalars ℝ) := by
  have h := hasMFDerivAt_self_iff_original_charts.mp hf
  apply hasMFDerivAt_self_iff_original_charts.mpr
  exact ⟨h.1, h.2.restrictScalars ℝ⟩

#print axioms hasMFDerivAt_real_of_complex
end HodgeLean.Foundations.TubularEuler
