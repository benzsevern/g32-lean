import Mathlib.Geometry.Manifold.ChartedSpace

noncomputable section
namespace HodgeLean.Adapters
open scoped Topology

/-- An open subset of a second countable charted space is covered by countably
many coordinate charts restricted to that same open subset. -/
theorem a3b4a_gysin_countable_restricted_chart_cover
    {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
    (V : Set M) (hV : IsOpen V) :
    ∃ J : Set M, J.Countable ∧ J ⊆ V ∧
      V = ⋃ z ∈ J, ((chartAt H z).restrOpen V hV).source := by
  have hnhds : ∀ z ∈ V,
      ((chartAt H z).restrOpen V hV).source ∈ nhdsWithin z V := by
    intro z hz
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (chart_source_mem_nhds H z))
      self_mem_nhdsWithin
  obtain ⟨J, hJV, hJ, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin hnhds
  refine ⟨J, hJ, hJV, Set.Subset.antisymm hcover ?_⟩
  intro z hz
  obtain ⟨j, _, hzj⟩ := Set.mem_iUnion₂.mp hz
  exact hzj.2

end HodgeLean.Adapters
