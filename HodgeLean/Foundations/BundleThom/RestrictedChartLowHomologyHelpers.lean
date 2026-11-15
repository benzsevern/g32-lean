import HodgeLean.Foundations.BundleThom.ChartLowHomologyHelpers
import HodgeLean.Foundations.BundleThom.ChartDomainGluingHelpers

/-! # Low-degree vanishing on actual intersections of bundle chart domains

Open restriction retains the supplied linear chart and its actual complement pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ]

/-- Open restriction of a supplied complex linear chart retains fibrewise linearity.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, restricted bundle charts. -/
theorem i1_chartRestrOpen_isLinear (s : Set B) (hs : IsOpen s) :
    (e.restrOpen s hs).IsLinear ℂ := by
  constructor
  intro b hb
  exact e.linear ℂ hb.1

/-- The source of the actual open-restricted chart is the original source intersected with the specified base preimage.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, restricted bundle charts. -/
theorem i1_chartRestrOpen_source (s : Set B) (hs : IsOpen s) :
    (e.restrOpen s hs).source = e.source ∩ TotalSpace.proj ⁻¹' s := by
  ext z
  rw [(e.restrOpen s hs).mem_source, Set.mem_inter_iff, e.mem_source]
  rfl

/-- The actual intersection pair of two positive-rank chart domains has zero degree-zero rational homology.
Source: Hatcher, Algebraic Topology, §2.1, relative product homology in bundle charts. -/
theorem i1_chartIntersectionRelativeHomologyZero_isZero (hk : 0 < k)
    (e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B)) :
    IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (e.source ∩ e'.source)) 0) := by
  let f := e.restrOpen e'.baseSet e'.open_baseSet
  letI : f.IsLinear ℂ := i1_chartRestrOpen_isLinear k E e _ _
  have hf : f.source = e.source ∩ e'.source := by
    rw [i1_chartRestrOpen_source]
    congr 1
    exact e'.source_eq.symm
  have h := i1_chartRelativeHomologyZero_isZero k E f hk
  rw [i1_chartPair_eq_actualDomain, hf] at h
  exact h


/-- The actual intersection pair of two positive-rank chart domains has zero degree-one rational homology.
Source: Hatcher, Algebraic Topology, §2.1, relative product homology in bundle charts. -/
theorem i1_chartIntersectionRelativeHomologyOne_isZero (hk : 0 < k)
    (e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B)) :
    IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (e.source ∩ e'.source)) 1) := by
  let f := e.restrOpen e'.baseSet e'.open_baseSet
  letI : f.IsLinear ℂ := i1_chartRestrOpen_isLinear k E e _ _
  have hf : f.source = e.source ∩ e'.source := by
    rw [i1_chartRestrOpen_source]
    congr 1
    exact e'.source_eq.symm
  have h := i1_chartRelativeHomologyOne_isZero k E f hk
  rw [i1_chartPair_eq_actualDomain, hf] at h
  exact h

end HodgeLean.Foundations.BundleThom
