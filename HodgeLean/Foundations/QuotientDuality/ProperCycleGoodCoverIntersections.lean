import HodgeLean.Foundations.QuotientDuality.ProperCycleCoverSubspaceModels

/-! # Literal finite intersections in the open cover induction -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Intersecting every member of a nonempty finite subfamily with one actual cover member is its literal intersection after adjoining that member.
Source: Hatcher, Algebraic Topology, section 4G, finite-cover intersections.
HC no distance; AV milestone no distance. -/
lemma properCycle_cover_intersection_adjoin
    {X I : Type} [DecidableEq I] (C : I → Set X) (a : I)
    (t : Finset I) (ht : t.Nonempty) :
    (⋂ i ∈ t, C a ∩ C i) = ⋂ i ∈ insert a t, C i := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h i hi
    rcases Finset.mem_insert.mp hi with he | hi
    · subst i
      obtain ⟨j, hj⟩ := ht
      exact (h j hj).1
    · exact (h i hi).2
  · intro h i hi
    exact ⟨h a (Finset.mem_insert_self a t), h i (Finset.mem_insert_of_mem hi)⟩

/-- An actual overlap cover has one fewer possible simultaneous member after adjoining its fixed cover member.
Source: Hatcher, Algebraic Topology, section 4G, the nerve of a finite cover.
HC no distance; AV milestone no distance. -/
lemma properCycle_cover_overlap_card_bound
    {X I : Type} [DecidableEq I] (C : I → Set X) (a : I)
    (s : Finset I) (ha : a ∉ s) (d : ℕ)
    (hmult : ∀ t : Finset I, t ⊆ insert a s → (⋂ i ∈ t, C i).Nonempty → t.card ≤ d + 2)
    (t : Finset I) (ht : t ⊆ s) (htX : (⋂ i ∈ t, C a ∩ C i).Nonempty) :
    t.card ≤ d + 1 := by
  by_cases htn : t.Nonempty
  · have ha' : a ∉ t := fun h => ha (ht h)
    rw [properCycle_cover_intersection_adjoin C a t htn] at htX
    have h := hmult (insert a t) (Finset.insert_subset_insert a ht) htX
    rw [Finset.card_insert_of_notMem ha'] at h
    omega
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htn
    subst t
    simp only [Finset.card_empty]
    omega

end HodgeLean.Foundations.QuotientDuality
