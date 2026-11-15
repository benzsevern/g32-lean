import HodgeLean.Foundations.BundleThom.PositiveRankFiniteThomExistenceHelpers
import HodgeLean.Foundations.BundleThom.EmptyPairCoclassHelpers
import HodgeLean.Foundations.BundleThom.ChartDomainGluingHelpers

/-! # Every-chart normalized Thom existence for compact-base complex bundles

Compactness extracts an actual finite chart cover; empty bases use the actual empty relative pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- Every actual positive-rank complex bundle over a compact base has a unique rational supported Thom class normalized on every complex linear chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom construction; Hatcher, Algebraic Topology, §4.D. -/
theorem i1_positiveRank_bundleThom_exists_unique {B : Type} [TopologicalSpace B] [CompactSpace B]
    (k : ℕ) (hk : 0 < k) (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E] :
    ∃! u : i1_supportedClass k E,
      ∀ (g : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
        (hg : g.IsLinear ℂ),
        relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E g) u = i1_chartOrientation k E g := by
  classical
  cases isEmpty_or_nonempty B with
  | inl hB =>
    letI := hB
    letI : IsEmpty (TotalSpace (Fin k → ℂ) E) := ⟨fun z => isEmptyElim z.proj⟩
    letI : IsEmpty (TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ).fst := by
      change IsEmpty (TotalSpace (Fin k → ℂ) E)
      infer_instance
    letI : Subsingleton (i1_supportedClass k E) :=
      i1_relativeCohomology_subsingleton_of_isEmpty
        (TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ) (2 * k)
    refine ⟨0, ?_, ?_⟩
    · intro g hg
      letI := hg
      letI : IsEmpty (i1_chartPair k E g).fst := by
        change IsEmpty g.source
        infer_instance
      letI := i1_relativeCohomology_subsingleton_of_isEmpty (i1_chartPair k E g) (2 * k)
      exact Subsingleton.elim _ _
    · intro u hu
      exact Subsingleton.elim _ _
  | inr hB =>
    letI := hB
    obtain ⟨s, hcover⟩ := i1_bundle_finite_chartSource_cover k E
    have hs : s.Nonempty := by
      obtain ⟨b, hb, _⟩ := hcover (zeroSection (Fin k → ℂ) E (Classical.arbitrary B))
      exact ⟨b, hb⟩
    let e := fun b : B => trivializationAt (Fin k → ℂ) E b
    haveI : ∀ b, (e b).IsLinear ℂ := by
      intro b
      dsimp [e]
      infer_instance
    exact i1_positiveRank_bundleThom_exists_unique_of_finite_cover k hk E e s hs hcover

end HodgeLean.Foundations.BundleThom
