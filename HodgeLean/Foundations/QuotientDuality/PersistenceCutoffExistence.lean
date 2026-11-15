import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UnitInterval

/-! Actual supported time cutoffs around points in open domains. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_neighbourhood_cutoff
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U) :
    ∃ (V S : Set X) (β : C(X, unitInterval)), IsOpen V ∧ x ∈ V ∧ IsClosed S ∧ S ⊆ U ∧
      (∀ y, y ∉ S → β y = 0) ∧ (∀ y ∈ V, β y = 1) := by
  obtain ⟨K, hK, _, hxK, hKU⟩ := exists_compact_closed_between isCompact_singleton hU
    (show ({x} : Set X) ⊆ U by simpa only [Set.singleton_subset_iff] using hx)
  obtain ⟨f, hfK, _, hfU, hfI⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let β : C(X, unitInterval) := ⟨fun y => ⟨f y, hfI y⟩, f.continuous.subtype_mk _⟩
  refine ⟨interior K, tsupport f, β, isOpen_interior, hxK (Set.mem_singleton x),
    isClosed_tsupport f, hfU, ?_, ?_⟩
  · intro y hy
    apply Subtype.ext
    change f y = 0
    by_contra h
    exact hy (subset_closure h)
  · intro y hy
    apply Subtype.ext
    exact hfK (interior_subset hy)

end HodgeLean.Foundations.QuotientDuality
