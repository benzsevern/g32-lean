import HodgeLean.Foundations.BundleThom.FiniteSingularIntersectionHelpers
import HodgeLean.Foundations.BundleThom.ChartRelativeVanishingHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativeHomologyVanishingTransferHelpers

/-! # Actual finite chart intersections

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B ι : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e : ι → Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))

/-- A finite intersection of actual chart sources is the exact preimage of the finite base intersection.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, saturated bundle chart domains. -/
theorem i1_chartFinsetInf_source (s : Finset ι) :
    s.inf (fun i => (e i).source) = TotalSpace.proj ⁻¹' s.inf (fun i => (e i).baseSet) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.inf_insert, (e a).source_eq, ih, Set.preimage_inter]
    rfl

/-- Every nonempty finite actual chart intersection has zero relative homology below twice the complex rank.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.2, restricted product chart coordinates. -/
theorem i1_chartFinsetIntersectionRelativeHomology_isZero_of_lt
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty) (n : ℕ) (hn : n < 2 * k) :
    IsZero (RelativeHomology ℚ
      (i1_subsetRelativePair (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ
        (s.inf (fun i => (e i).source))) n) := by
  classical
  obtain ⟨a, ha⟩ := hs
  have ho : IsOpen (s.inf (fun i => (e i).baseSet)) := by
    clear ha a
    induction s using Finset.induction_on with
    | empty => exact isOpen_univ
    | @insert i t hi iht =>
      rw [Finset.inf_insert]
      exact (e i).open_baseSet.inter iht
  have he : (e a).source ∩ TotalSpace.proj ⁻¹' s.inf (fun i => (e i).baseSet) =
      s.inf (fun i => (e i).source) := by
    rw [i1_chartFinsetInf_source]
    apply Set.inter_eq_right.mpr
    intro z hz
    rw [(e a).mem_source]
    exact (Finset.inf_le (f := fun i => (e i).baseSet) ha) hz
  rw [← he]
  exact i1_chartBaseRestrictionRelativeHomology_isZero_of_lt k E (e a) n hn _ ho

/-- Every nonempty finite intersection of actual chart singular ranges has zero relative homology below twice the complex rank.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.2, actual relative singular coordinates. -/
theorem i1_chartFinsetRangeIntersectionHomology_isZero_of_lt
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty) (n : ℕ) (hn : n < 2 * k) :
    IsZero (((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
      (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).obj
      (s.inf (fun i => i1_singularSubsetRange (i1_totalSpace k E) (e i).source))).homology n) := by
  rw [i1_singularSubsetRange_finsetInf]
  exact (i1_subsetRelativeHomology_isZero_iff_range (i1_totalSpace k E)
    (i1_zeroSupport k E)ᶜ (s.inf (fun i => (e i).source)) n).mp
      (i1_chartFinsetIntersectionRelativeHomology_isZero_of_lt k E e s hs n hn)

end HodgeLean.Foundations.BundleThom
