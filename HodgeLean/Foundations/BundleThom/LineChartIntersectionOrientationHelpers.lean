import HodgeLean.Foundations.BundleThom.ChartIntersectionProductHelpers
import HodgeLean.Foundations.BundleThom.RelativePairIsoCoclassHelpers

/-! # Orientation compatibility on actual line-bundle chart intersections

The equality is on the exact relative intersection pair used by the gluing interface.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- The two specified complex line-chart orientations agree after restriction to their actual relative intersection pair.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, oriented Thom gluing; Hatcher, §2.2 and §3.1. -/
theorem i1_lineChartOrientations_actualIntersection_compatible
    {B : Type} [TopologicalSpace B] (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
    [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E]
    (e e' : Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] :
    relativeCohomologyMap ℚ 2
        (i1_subsetRelativePairMap (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ
          (Set.inter_subset_left : e.source ∩ e'.source ⊆ e.source))
        (i1_chartOrientation 1 E e) =
      relativeCohomologyMap ℚ 2
        (i1_subsetRelativePairMap (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ
          (Set.inter_subset_right : e.source ∩ e'.source ⊆ e'.source))
        (i1_chartOrientation 1 E e') := by
  apply i1_relativeCohomologyMap_iso_injective (i1_chartIntersectionProductIso 1 E e e').symm 2
  rw [Iso.symm_hom]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartIntersectionProductIso_inv_comp_chart 1 E e e' e Set.inter_subset_left,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartIntersectionProductIso_inv_comp_chart 1 E e e' e' Set.inter_subset_right]
  exact (i1_chartOrientations_lineOverlap_compatible E e e'
    (id : ↥(e.baseSet ∩ e'.baseSet) → ↥(e.baseSet ∩ e'.baseSet)) continuous_id).symm

end HodgeLean.Foundations.BundleThom
