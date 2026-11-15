import HodgeLean.Foundations.BundleThom.RestrictedChartLowHomologyHelpers
import HodgeLean.Foundations.BundleThom.LineChartOverlapHelpers

/-! # Actual product coordinates on bundle chart intersections

The source is the supplied intersection domain with its inherited zero-section complement.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ]

/-- The actual relative pair on two chart sources has product coordinates over their actual base intersection.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, restricted bundle chart coordinates. -/
def i1_chartIntersectionProductIso :
    i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ (e.source ∩ e'.source) ≅
      i1_productNormalPair ↥(e.baseSet ∩ e'.baseSet) k := by
  let r := e.restrOpen e'.baseSet e'.open_baseSet
  letI : r.IsLinear ℂ := i1_chartRestrOpen_isLinear k E e _ _
  have hs : r.source = e.source ∩ e'.source := by
    rw [i1_chartRestrOpen_source]
    congr 1
    exact e'.source_eq.symm
  let h : ↥(e.source ∩ e'.source) ≃ₜ (↥(e.baseSet ∩ e'.baseSet) × (Fin k → ℂ)) :=
    (Homeomorph.setCongr hs.symm).trans r.sourceHomeomorphBaseSetProd
  exact TopPair.isoOfSubset h (by
    intro v
    have hv : v.1 ∈ r.source := hs.symm ▸ v.2
    change (r.sourceHomeomorphBaseSetProd ⟨v.1, hv⟩).2 ≠ 0 ↔ v.1.2 ≠ 0
    rw [r.sourceHomeomorphBaseSetProd_apply]
    apply not_congr
    change (r.continuousLinearEquivAt ℂ v.1.proj (r.mem_source.mp hv)) v.1.2 = 0 ↔ v.1.2 = 0
    constructor
    · intro hz
      apply (r.continuousLinearEquivAt ℂ v.1.proj (r.mem_source.mp hv)).injective
      simpa only [map_zero] using hz
    · intro hz
      rw [hz, map_zero])

/-- Actual chart-intersection product coordinates commute with inclusion into any supplied chart containing the base intersection.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, naturality of overlap coordinates. -/
theorem i1_chartIntersectionProductIso_inv_comp_chart
    (g : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [g.IsLinear ℂ] (hg : e.baseSet ∩ e'.baseSet ⊆ g.baseSet) :
    (i1_chartIntersectionProductIso k E e e').inv ≫
      i1_subsetRelativePairMap (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (show e.source ∩ e'.source ⊆ g.source from fun z hz =>
          g.mem_source.mpr (hg ⟨e.mem_source.mp hz.1, e'.mem_source.mp hz.2⟩)) =
      i1_chartProductPairMap k E e g
        (Subtype.val : ↥(e.baseSet ∩ e'.baseSet) → B) continuous_subtype_val
        (fun b => b.2.1) (fun b => hg b.2) := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change e.toOpenPartialHomeomorph.symm (z.1.1.1, z.1.2) = _
    exact (e.mk_symm z.1.1.2.1 z.1.2).symm
  · apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change e.toOpenPartialHomeomorph.symm (z.1.1, z.2) = _
    exact (e.mk_symm z.1.2.1 z.2).symm

end HodgeLean.Foundations.BundleThom
