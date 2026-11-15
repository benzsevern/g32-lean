import HodgeLean.Foundations.BundleThom.ChartBaseRestrictionHomologyHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativeHomologyVanishingTransferHelpers

/-! # Low homology of actual chart-intersection singular-range quotients

One supplied linear chart gives product coordinates on each actual multiple intersection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (g e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [g.IsLinear ℂ]

/-- Triple actual chart-range intersections have zero degree-one homology relative to the zero-section complement in positive rank.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, relative product homology in chart intersections. -/
theorem i1_chartTripleRangeHomologyOne_isZero (hk : 0 < k) :
    IsZero (((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
      (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).obj
      (i1_singularSubsetRange (i1_totalSpace k E) g.source ⊓
        i1_singularSubsetRange (i1_totalSpace k E) e.source ⊓
        i1_singularSubsetRange (i1_totalSpace k E) e'.source)).homology 1) := by
  have hh := i1_chartBaseRestrictionRelativeHomologyOne_isZero k E g hk
    (e.baseSet ∩ e'.baseSet) (e.open_baseSet.inter e'.open_baseSet)
  have hs : g.source ∩ TotalSpace.proj ⁻¹' (e.baseSet ∩ e'.baseSet) =
      g.source ∩ (e.source ∩ e'.source) := by
    rw [e.source_eq, e'.source_eq, Set.preimage_inter]
  rw [hs] at hh
  have hr := (i1_subsetRelativeHomology_isZero_iff_range (i1_totalSpace k E)
    (i1_zeroSupport k E)ᶜ (g.source ∩ (e.source ∩ e'.source)) 1).mp hh
  rw [i1_singularSubsetRange_inter, i1_singularSubsetRange_inter] at hr
  simpa only [inf_assoc] using hr

/-- Quadruple actual chart-range intersections have zero degree-zero homology relative to the zero-section complement in positive rank.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, relative product homology in chart intersections. -/
theorem i1_chartQuadrupleRangeHomologyZero_isZero
    (e'' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    (hk : 0 < k) :
    IsZero (((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
      (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).obj
      (i1_singularSubsetRange (i1_totalSpace k E) g.source ⊓
        i1_singularSubsetRange (i1_totalSpace k E) e.source ⊓
        i1_singularSubsetRange (i1_totalSpace k E) e'.source ⊓
        i1_singularSubsetRange (i1_totalSpace k E) e''.source)).homology 0) := by
  have hh := i1_chartBaseRestrictionRelativeHomologyZero_isZero k E g hk
    (e.baseSet ∩ e'.baseSet ∩ e''.baseSet)
    ((e.open_baseSet.inter e'.open_baseSet).inter e''.open_baseSet)
  have hs : g.source ∩ TotalSpace.proj ⁻¹' (e.baseSet ∩ e'.baseSet ∩ e''.baseSet) =
      g.source ∩ (e.source ∩ e'.source ∩ e''.source) := by
    simp only [e.source_eq, e'.source_eq, e''.source_eq, Set.preimage_inter]
  rw [hs] at hh
  have hr := (i1_subsetRelativeHomology_isZero_iff_range (i1_totalSpace k E)
    (i1_zeroSupport k E)ᶜ (g.source ∩ (e.source ∩ e'.source ∩ e''.source)) 0).mp hh
  rw [i1_singularSubsetRange_inter, i1_singularSubsetRange_inter,
    i1_singularSubsetRange_inter] at hr
  simpa only [inf_assoc] using hr

end HodgeLean.Foundations.BundleThom
