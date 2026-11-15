import HodgeLean.Foundations.BundleThom.RankOneFiniteThomExistenceHelpers
import HodgeLean.Foundations.BundleThom.EmptyPairCoclassHelpers
import HodgeLean.Foundations.BundleThom.ChartDomainGluingHelpers

/-! # Every-chart normalized Thom existence for compact-base complex line bundles

Compactness extracts an actual finite chart cover; empty bases use the actual empty relative pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- Every actual complex line bundle over a compact base has a unique rational supported Thom class normalized on every complex linear chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom construction; Hatcher, Algebraic Topology, §4.D. -/
theorem i1_rankOne_bundleThom_exists_unique {B : Type} [TopologicalSpace B] [CompactSpace B]
    (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
    [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E] :
    ∃! u : i1_supportedClass 1 E,
      ∀ (g : Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
        (hg : g.IsLinear ℂ),
        relativeCohomologyMap ℚ 2 (i1_chartInclusion 1 E g) u = i1_chartOrientation 1 E g := by
  classical
  cases isEmpty_or_nonempty B with
  | inl hB =>
    letI := hB
    letI : IsEmpty (TotalSpace (Fin 1 → ℂ) E) := ⟨fun z => isEmptyElim z.proj⟩
    letI : IsEmpty (TopPair.ofSubset (X := i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ).fst := by
      change IsEmpty (TotalSpace (Fin 1 → ℂ) E)
      infer_instance
    letI : Subsingleton (i1_supportedClass 1 E) :=
      i1_relativeCohomology_subsingleton_of_isEmpty
        (TopPair.ofSubset (X := i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ) 2
    refine ⟨0, ?_, ?_⟩
    · intro g hg
      letI := hg
      letI : IsEmpty (i1_chartPair 1 E g).fst := by
        change IsEmpty g.source
        infer_instance
      letI := i1_relativeCohomology_subsingleton_of_isEmpty (i1_chartPair 1 E g) 2
      exact Subsingleton.elim _ _
    · intro u hu
      exact Subsingleton.elim _ _
  | inr hB =>
    letI := hB
    obtain ⟨s, hcover⟩ := i1_bundle_finite_chartSource_cover 1 E
    have hs : s.Nonempty := by
      obtain ⟨b, hb, _⟩ := hcover (zeroSection (Fin 1 → ℂ) E (Classical.arbitrary B))
      exact ⟨b, hb⟩
    let e := fun b : B => trivializationAt (Fin 1 → ℂ) E b
    haveI : ∀ b, (e b).IsLinear ℂ := by
      intro b
      dsimp [e]
      infer_instance
    exact i1_rankOne_bundleThom_exists_unique_of_finite_cover E e s hs hcover

end HodgeLean.Foundations.BundleThom
