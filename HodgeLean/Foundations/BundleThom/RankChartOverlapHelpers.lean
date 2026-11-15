import HodgeLean.Foundations.BundleThom.ProductMatrixSuccessorOrientationHelpers
import HodgeLean.Foundations.BundleThom.ChartOverlapPairHelpers

/-! # Actual bundle-chart orientation comparison over arbitrary parametrized overlaps

Both chart maps and the supplied parameter map remain in the comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

/-- Two actual complex bundle chart orientations agree over every supplied parametrized overlap.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex transition invariance; Hatcher, §2.2 and §3.1. -/
theorem i1_chartOrientations_rankOverlap_compatible
    {B T : Type} [TopologicalSpace B] [TopologicalSpace T]
    (k : ℕ) (hk : 0 < k) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] [e'.IsLinear ℂ]
    (f : T → ↥(e.baseSet ∩ e'.baseSet)) (hf : Continuous f) :
    relativeCohomologyMap ℚ (2 * k) (i1_chartOverlapProductPairMap k E e e' f hf)
      (i1_chartOrientation k E e') =
    relativeCohomologyMap ℚ (2 * k)
      (i1_chartProductPairMap k E e e (fun t => (f t).1) (continuous_subtype_val.comp hf)
        (fun t => (f t).2.1) (fun t => (f t).2.1)) (i1_chartOrientation k E e) := by
  rw [i1_chartOrientation_productPullback k E e (fun t => (f t).1)
    (continuous_subtype_val.comp hf) (fun t => (f t).2.1)]
  change relativeCohomologyMap ℚ (2 * k) _
    (relativeCohomologyMap ℚ (2 * k) (i1_chartNormal k E e') (normalizedPointCoclass k)) = _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartOverlapProductPairMap_comp_normal]
  exact i1_productMatrixNormalMap_thomDegree_pullback k hk _ _ _
    (normalizedPointCoclass k)

end HodgeLean.Foundations.BundleThom
