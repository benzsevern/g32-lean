import HodgeLean.Foundations.BundleThom.ProductMatrixDegreeTwoOrientationHelpers
import HodgeLean.Foundations.BundleThom.ChartOverlapPairHelpers

/-! # Actual line-chart orientation comparison over arbitrary parametrized overlaps

Both chart maps and the supplied parameter map remain in the comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

/-- Two actual line-bundle chart orientations agree over every supplied parametrized overlap.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex transition invariance; Hatcher, §2.2 and §3.1. -/
theorem i1_chartOrientations_lineOverlap_compatible
    {B T : Type} [TopologicalSpace B] [TopologicalSpace T]
    (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
    [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E]
    (e e' : Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
    [e.IsLinear ℂ] [e'.IsLinear ℂ]
    (f : T → ↥(e.baseSet ∩ e'.baseSet)) (hf : Continuous f) :
    relativeCohomologyMap ℚ 2 (i1_chartOverlapProductPairMap 1 E e e' f hf)
      (i1_chartOrientation 1 E e') =
    relativeCohomologyMap ℚ 2
      (i1_chartProductPairMap 1 E e e (fun t => (f t).1) (continuous_subtype_val.comp hf)
        (fun t => (f t).2.1) (fun t => (f t).2.1)) (i1_chartOrientation 1 E e) := by
  rw [i1_chartOrientation_productPullback 1 E e (fun t => (f t).1)
    (continuous_subtype_val.comp hf) (fun t => (f t).2.1)]
  change relativeCohomologyMap ℚ 2 _
    (relativeCohomologyMap ℚ 2 (i1_chartNormal 1 E e') (normalizedPointCoclass 1)) = _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartOverlapProductPairMap_comp_normal]
  exact i1_productMatrixNormalMap_degreeTwo_pullback 1 (by omega) _ _ _
    (normalizedPointCoclass 1)

end HodgeLean.Foundations.BundleThom
