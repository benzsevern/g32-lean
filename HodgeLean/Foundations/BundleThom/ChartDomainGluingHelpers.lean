import HodgeLean.Foundations.BundleThom.ActualRelativeBinaryUniqueExtensionHelpers
import HodgeLean.Foundations.BundleThom.Defs

/-! # Actual bundle chart domains in relative coclass gluing -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]

/-- The specified bundle chart pair is the actual domain pair for the zero-section complement.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, relative chart pairs. -/
theorem i1_chartPair_eq_actualDomain
    (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] :
    i1_chartPair k E e = i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ e.source := rfl

/-- The specified chart inclusion is exactly the actual relative-domain inclusion used in gluing.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, chart restriction. -/
theorem i1_chartInclusion_eq_actualDomainInclusion
    (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] :
    i1_chartInclusion k E e =
      i1_subsetRelativePairInclusion (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ e.source := rfl

/-- Compactness of the base supplies finitely many actual complex bundle chart sources covering every fibre.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, finite bundle chart covers. -/
theorem i1_bundle_finite_chartSource_cover [CompactSpace B] :
    ∃ s : Finset B, ∀ z : TotalSpace (Fin k → ℂ) E,
      ∃ b ∈ s, z ∈ (trivializationAt (Fin k → ℂ) E b).source := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B => (trivializationAt (Fin k → ℂ) E b).baseSet)
    (fun b => (trivializationAt (Fin k → ℂ) E b).open_baseSet) (by
      intro b _
      exact Set.mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt (Fin k → ℂ) E b⟩)
  refine ⟨s, fun z => ?_⟩
  obtain ⟨b, hb, hz⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z.proj))
  exact ⟨b, hb, (trivializationAt (Fin k → ℂ) E b).mem_source.mpr hz⟩

end HodgeLean.Foundations.BundleThom
