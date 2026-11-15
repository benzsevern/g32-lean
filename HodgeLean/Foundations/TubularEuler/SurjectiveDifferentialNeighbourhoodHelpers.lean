import HodgeLean.Foundations.TubularEuler.NormalMetricLiftHelpers
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Persistence of a surjective transverse differential

A fixed right inverse reduces the neighbourhood claim to openness of invertibility.
HC no distance; AV milestone no distance. -/

noncomputable section
open Topology
namespace HodgeLean.Foundations.TubularEuler

theorem surjective_eventually_of_continuousAt
    {𝕜 : Type*} [RCLike 𝕜]
    {E N B : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup N] [InnerProductSpace 𝕜 N] [CompleteSpace N]
    [FiniteDimensional 𝕜 N] [TopologicalSpace B]
    (D : B → E →L[𝕜] N) (p : B) (hc : ContinuousAt D p)
    (hp : Function.Surjective (D p)) :
    ∀ᶠ q in 𝓝 p, Function.Surjective (D q) := by
  let R := normalMetricLift (D p)
  have hR : (D p).comp R = ContinuousLinearMap.id 𝕜 N := by
    ext n
    exact normalMetricLift_rightInverse (D p) hp n
  have hI : ((D p).comp R).IsInvertible := by
    rw [hR]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 N, rfl⟩
  have hc' : ContinuousAt (fun q => (D q).comp R) p := hc.clm_comp continuousAt_const
  filter_upwards [hc' hI.eventually_nhds] with q hq
  obtain ⟨e, he⟩ := hq
  change e.toContinuousLinearMap = (D q).comp R at he
  intro n
  refine ⟨R (e.symm n), ?_⟩
  change ((D q).comp R) (e.symm n) = n
  rw [← he]
  exact e.apply_symm_apply n

#print axioms surjective_eventually_of_continuousAt

theorem finite_target_surjective_eventually_of_continuousAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E N B : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup N] [NormedSpace 𝕜 N] [CompleteSpace N]
    [FiniteDimensional 𝕜 N] [TopologicalSpace B]
    (D : B → E →L[𝕜] N) (p : B) (hc : ContinuousAt D p)
    (hp : Function.Surjective (D p)) :
    ∀ᶠ q in 𝓝 p, Function.Surjective (D q) := by
  obtain ⟨r, hr⟩ := (D p).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hp)
  let R := r.toContinuousLinearMap
  have hR : (D p).comp R = ContinuousLinearMap.id 𝕜 N := by
    ext n
    exact LinearMap.congr_fun hr n
  have hI : ((D p).comp R).IsInvertible := by
    rw [hR]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 N, rfl⟩
  have hc' : ContinuousAt (fun q => (D q).comp R) p := hc.clm_comp continuousAt_const
  filter_upwards [hc' hI.eventually_nhds] with q hq
  obtain ⟨e, he⟩ := hq
  change e.toContinuousLinearMap = (D q).comp R at he
  intro n
  refine ⟨R (e.symm n), ?_⟩
  change ((D q).comp R) (e.symm n) = n
  rw [← he]
  exact e.apply_symm_apply n

#print axioms finite_target_surjective_eventually_of_continuousAt

end HodgeLean.Foundations.TubularEuler
