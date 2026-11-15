import HodgeLean.Foundations.BundleThom.RankChartOverlapHelpers
import HodgeLean.Foundations.BundleThom.ChartIntersectionProductHelpers
import HodgeLean.Foundations.BundleThom.RelativePairIsoCoclassHelpers

/-! # Orientation compatibility on actual complex bundle chart intersections

The equality is on the exact relative intersection pair used by the gluing interface.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- The two specified complex bundle chart orientations agree after restriction to their actual relative intersection pair.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, oriented Thom gluing; Hatcher, §2.2 and §3.1. -/
theorem i1_rankChartOrientations_actualIntersection_compatible
    {B : Type} [TopologicalSpace B] (k : ℕ) (hk : 0 < k) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] :
    relativeCohomologyMap ℚ (2 * k)
        (i1_subsetRelativePairMap (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
          (Set.inter_subset_left : e.source ∩ e'.source ⊆ e.source))
        (i1_chartOrientation k E e) =
      relativeCohomologyMap ℚ (2 * k)
        (i1_subsetRelativePairMap (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
          (Set.inter_subset_right : e.source ∩ e'.source ⊆ e'.source))
        (i1_chartOrientation k E e') := by
  apply i1_relativeCohomologyMap_iso_injective (i1_chartIntersectionProductIso k E e e').symm (2 * k)
  rw [Iso.symm_hom]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartIntersectionProductIso_inv_comp_chart k E e e' e Set.inter_subset_left,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartIntersectionProductIso_inv_comp_chart k E e e' e' Set.inter_subset_right]
  exact (i1_chartOrientations_rankOverlap_compatible k hk E e e'
    (id : ↥(e.baseSet ∩ e'.baseSet) → ↥(e.baseSet ∩ e'.baseSet)) continuous_id).symm

end HodgeLean.Foundations.BundleThom
