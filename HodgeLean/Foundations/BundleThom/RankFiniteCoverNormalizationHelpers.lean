import HodgeLean.Foundations.BundleThom.RankFiniteCoverThomHelpers
import HodgeLean.Foundations.BundleThom.RankFiniteCoverCoclassDetectionHelpers

/-! # Every-chart normalization from finite actual complex chart covers

Adjoining a supplied chart constructs a second class, and the original cover detects equality of the two classes.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- A supported complex complex bundle class normalized on a nonempty finite actual chart cover is normalized on every supplied complex linear chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, uniqueness of Thom normalization; Hatcher, §2.2 and §3.1. -/
theorem i1_rankFiniteCoverThom_allChartNormalization {B ι : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : ι → Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty)
    (hcover : ∀ z : TotalSpace (Fin k → ℂ) E, ∃ i ∈ s, z ∈ (e i).source)
    (u : i1_supportedClass k E)
    (hu : ∀ i ∈ s, relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E (e i)) u =
      i1_chartOrientation k E (e i))
    (g : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [g.IsLinear ℂ] :
    relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E g) u = i1_chartOrientation k E g := by
  classical
  let e' : Option ι → Trivialization (Fin k → ℂ)
      (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B) := fun o =>
    match o with
    | none => g
    | some i => e i
  haveI : ∀ o, (e' o).IsLinear ℂ := by
    intro o
    cases o with
    | none => change g.IsLinear ℂ; infer_instance
    | some i => change (e i).IsLinear ℂ; infer_instance
  let t : Finset (Option ι) := insert none (s.image some)
  have htn : t.Nonempty := ⟨none, Finset.mem_insert_self _ _⟩
  have hsome (i : ι) (hi : i ∈ s) : some i ∈ t :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have htc : ∀ z : TotalSpace (Fin k → ℂ) E, ∃ o ∈ t, z ∈ (e' o).source := by
    intro z
    obtain ⟨i, hi, hz⟩ := hcover z
    exact ⟨some i, hsome i hi, hz⟩
  obtain ⟨v, hv⟩ := i1_rankFiniteCoverThom_exists k hk E e' t htn htc
  have hvu : v = u := by
    apply i1_rankFiniteCoverCoclass_ext k hk E e s hs hcover
    intro i hi
    have hvi : relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E (e i)) v =
        i1_chartOrientation k E (e i) := hv (some i) (hsome i hi)
    exact hvi.trans (hu i hi).symm
  have hvg : relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E g) v =
      i1_chartOrientation k E g := hv none (Finset.mem_insert_self _ _)
  rw [hvu] at hvg
  exact hvg

end HodgeLean.Foundations.BundleThom
