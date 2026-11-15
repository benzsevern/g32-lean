import HodgeLean.Foundations.BundleThom.LineFiniteCoverNormalizationHelpers

/-! # Every-chart normalized Thom existence from finite actual line-chart covers

The finite cover constructs one supported class and detects its uniqueness globally.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- A complex line bundle with a nonempty finite actual linear chart cover has a unique rational supported class normalized on every complex linear chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom construction; Hatcher, Algebraic Topology, §4.D. -/
theorem i1_rankOne_bundleThom_exists_unique_of_finite_cover {B ι : Type} [TopologicalSpace B]
    (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
    [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E]
    (e : ι → Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty)
    (hcover : ∀ z : TotalSpace (Fin 1 → ℂ) E, ∃ i ∈ s, z ∈ (e i).source) :
    ∃! u : i1_supportedClass 1 E,
      ∀ (g : Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
        (hg : g.IsLinear ℂ),
        relativeCohomologyMap ℚ 2 (i1_chartInclusion 1 E g) u = i1_chartOrientation 1 E g := by
  obtain ⟨u, hu⟩ := i1_lineFiniteCoverThom_exists E e s hs hcover
  refine ⟨u, ?_, ?_⟩
  · intro g hg
    letI := hg
    exact i1_lineFiniteCoverThom_allChartNormalization E e s hs hcover u hu g
  · intro v hv
    apply i1_lineFiniteCoverCoclass_ext E e s hs hcover
    intro i hi
    exact (hv (e i) inferInstance).trans (hu i hi).symm

end HodgeLean.Foundations.BundleThom
