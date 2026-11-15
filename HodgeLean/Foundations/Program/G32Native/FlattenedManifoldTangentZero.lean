import HodgeLean.Foundations.Program.G32Native.SelfChartDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Tangent annihilation in the specified manifold flattening -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold
open Filter Topology
namespace HodgeLean.Foundations.TubularEuler

theorem flattened_manifold_tangent_transverse_zero
    {K B E N Q M : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup B] [NormedSpace K B]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup N] [NormedSpace K N]
    [TopologicalSpace Q] [ChartedSpace B Q]
    [TopologicalSpace M] [ChartedSpace E M]
    (σ : Q → M) (a : M → B × N) (x : Q)
    (S : B →L[K] E) (A : E →L[K] B × N)
    (hσ : HasMFDerivAt 𝓘(K, B) 𝓘(K, E) σ x S)
    (ha : HasMFDerivAt 𝓘(K, E) 𝓘(K, B × N) a (σ x) A)
    (hzero : ∀ᶠ y in 𝓝 x, (a (σ y)).2 = 0) :
    ((ContinuousLinearMap.snd K B N).comp A).comp S = 0 := by
  have hsnd : HasMFDerivAt 𝓘(K, B × N) 𝓘(K, N) Prod.snd (a (σ x))
      (ContinuousLinearMap.snd K B N) := by
    apply hasMFDerivAt_self_iff_original_charts.mpr
    refine ⟨continuous_snd.continuousAt, ?_⟩
    convert (ContinuousLinearMap.snd K B N).hasFDerivAt (x := a (σ x)) using 1 <;> rfl
  have hcomp := hsnd.comp x (ha.comp x hσ)
  have hz : HasMFDerivAt 𝓘(K, B) 𝓘(K, N) (fun y => (a (σ y)).2)  x 0 :=
    (hasMFDerivAt_const (0 : N) x).congr_of_eventuallyEq_abuse hzero
  convert hasMFDerivAt_unique hcomp hz using 1 <;> rfl

#print axioms flattened_manifold_tangent_transverse_zero
end HodgeLean.Foundations.TubularEuler
