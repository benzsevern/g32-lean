import HodgeLean.Foundations.BundleThom.RankFiniteCoverNormalizationHelpers

/-! # Every-chart normalized Thom existence from finite actual complex chart covers

The finite cover constructs one supported class and detects its uniqueness globally.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- A complex bundle with a nonempty finite actual linear chart cover has a unique rational supported class normalized on every complex linear chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom construction; Hatcher, Algebraic Topology, §4.D. -/
theorem i1_positiveRank_bundleThom_exists_unique_of_finite_cover {B ι : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : ι → Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty)
    (hcover : ∀ z : TotalSpace (Fin k → ℂ) E, ∃ i ∈ s, z ∈ (e i).source) :
    ∃! u : i1_supportedClass k E,
      ∀ (g : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
        (hg : g.IsLinear ℂ),
        relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E g) u = i1_chartOrientation k E g := by
  obtain ⟨u, hu⟩ := i1_rankFiniteCoverThom_exists k hk E e s hs hcover
  refine ⟨u, ?_, ?_⟩
  · intro g hg
    letI := hg
    exact i1_rankFiniteCoverThom_allChartNormalization k hk E e s hs hcover u hu g
  · intro v hv
    apply i1_rankFiniteCoverCoclass_ext k hk E e s hs hcover
    intro i hi
    exact (hv (e i) inferInstance).trans (hu i hi).symm

end HodgeLean.Foundations.BundleThom
