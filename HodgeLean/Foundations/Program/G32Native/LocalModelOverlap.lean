import Mathlib.Topology.Neighborhoods

/-! # Overlap of specified original local models of the same pointwise map -/
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Original local models of the same pointwise function agree locally
at every indexed point in a sufficiently small original open neighborhood. -/
theorem eventuallyEq_local_models_on_neighbourhood
    {I X Y : Type*} [TopologicalSpace X] (p : I → X) (f : I → X → Y) (b : X → Y)
    (h : ∀ i, f i =ᶠ[𝓝 (p i)] b) (i : I) :
    ∃ U : Set X, IsOpen U ∧ p i ∈ U ∧
      ∀ j, p j ∈ U → f i =ᶠ[𝓝 (p j)] f j := by
  obtain ⟨U, hU, hUopen, hUi⟩ := mem_nhds_iff.mp (h i)
  refine ⟨U, hUopen, hUi, ?_⟩
  intro j hj
  have hi : f i =ᶠ[𝓝 (p j)] b := Filter.mem_of_superset (hUopen.mem_nhds hj) hU
  exact hi.trans (h j).symm

#print axioms eventuallyEq_local_models_on_neighbourhood
end HodgeLean.Foundations.Program.G32Native
