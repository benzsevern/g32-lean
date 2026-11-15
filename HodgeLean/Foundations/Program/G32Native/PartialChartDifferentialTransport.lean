import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! # Transport of a function differential between original partial charts

The coordinate functions agree on the actual overlap near the reference point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.TubularEuler

/-- Differentiating the same function in two partial charts gives covector
transport by the actual coordinate-transition derivative.
Source: Mathlib, `HasFDerivAt.comp`, `HasFDerivAt.congr_of_eventuallyEq`,
and the inverse laws of `OpenPartialHomeomorph`.
HC no distance; AV milestone no distance. -/
theorem partialChart_differential_transport
    {𝕜 M E E' F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (a : OpenPartialHomeomorph M E) (b : OpenPartialHomeomorph M E')
    (x : M) (hxa : x ∈ a.source) (hxb : x ∈ b.source) (f : M → F)
    (A : E →L[𝕜] F) (B : E' →L[𝕜] F) (H : E →L[𝕜] E')
    (hA : HasFDerivAt (fun t => f (a.symm t)) A (a x))
    (hB : HasFDerivAt (fun t => f (b.symm t)) B (b x))
    (hH : HasFDerivAt (fun t => b (a.symm t)) H (a x)) :
    A = B.comp H := by
  have hpoint : b (a.symm (a x)) = b x := congrArg b (a.left_inv hxa)
  have hB' : HasFDerivAt (fun t => f (b.symm t)) B (b (a.symm (a x))) := by
    rw [hpoint]
    exact hB
  have hcomp := hB'.comp (a x) hH
  have hpre : ∀ᶠ t in 𝓝 (a x), a.symm t ∈ b.source :=
    (a.symm.continuousAt (a.map_source hxa)).eventually
      (b.open_source.mem_nhds (by simpa only [a.left_inv hxa] using hxb))
  have heq : (fun t => f (a.symm t)) =ᶠ[𝓝 (a x)]
      (fun t => f (b.symm (b (a.symm t)))) := by
    filter_upwards [hpre] with t ht
    exact (congrArg f (b.left_inv ht)).symm
  exact hA.unique (hcomp.congr_of_eventuallyEq heq)

#print axioms partialChart_differential_transport

end HodgeLean.Foundations.TubularEuler
