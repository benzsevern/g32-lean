import HodgeLean.Foundations.QuotientDuality.ProperCycleGoodCoverIntersections

/-! # Ordinary homology dimension from actual finite good covers -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A finite open cover with contractible nonempty intersections and multiplicity at most d+1 has zero ordinary rational homology above d.
Source: Hatcher, Algebraic Topology, sections 2.2 and 4G, finite good covers and Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_good_cover_homology_vanishes
    {I : Type} [DecidableEq I] (X : TopCat.{0}) (C : I → Set X)
    (s : Finset I) (d : ℕ)
    (hopen : ∀ i ∈ s, IsOpen (C i))
    (hgood : ∀ t : Finset I, t ⊆ s → t.Nonempty →
      IsEmpty ↥(⋂ i ∈ t, C i) ∨ ContractibleSpace ↥(⋂ i ∈ t, C i))
    (hmult : ∀ t : Finset I, t ⊆ s → (⋂ i ∈ t, C i).Nonempty → t.card ≤ d + 1)
    (n : ℕ) (hn : d < n) :
    Subsingleton (Homology ℚ (TopCat.of ↥(⋃ i ∈ s, C i)) n) := by
  classical
  induction s using Finset.induction_on generalizing X C d n with
  | empty =>
    letI : IsEmpty ↥(⋃ i ∈ (∅ : Finset I), C i) := ⟨fun x => by simpa using x.property⟩
    exact properCycle_empty_homology_subsingleton _ n
  | @insert a s ha ih =>
    cases n with
    | zero => omega
    | succ q =>
      let S : Set X := ⋃ i ∈ s, C i
      let T : Set X := C a ∪ S
      have hT : (⋃ i ∈ insert a s, C i) = T := by ext x; simp [T, S]
      rw [hT]
      let Z := TopCat.of T
      let U : Set Z := {x | x.val ∈ C a}
      let V : Set Z := {x | x.val ∈ S}
      have hSopen : IsOpen S := isOpen_iUnion fun i => isOpen_iUnion fun hi =>
        hopen i (Finset.mem_insert_of_mem hi)
      have hUopen : IsOpen U := (hopen a (Finset.mem_insert_self a s)).preimage continuous_subtype_val
      have hVopen : IsOpen V := hSopen.preimage continuous_subtype_val
      have hcover : U ∪ V = Set.univ := Set.eq_univ_iff_forall.mpr fun x => x.property
      have hsGood : ∀ t : Finset I, t ⊆ s → t.Nonempty →
          IsEmpty ↥(⋂ i ∈ t, C i) ∨ ContractibleSpace ↥(⋂ i ∈ t, C i) :=
        fun t ht => hgood t (ht.trans (Finset.subset_insert a s))
      have hsMult : ∀ t : Finset I, t ⊆ s → (⋂ i ∈ t, C i).Nonempty → t.card ≤ d + 1 :=
        fun t ht => hmult t (ht.trans (Finset.subset_insert a s))
      have hS : Subsingleton (Homology ℚ (TopCat.of S) (q + 1)) := by
        apply ih (d := d)
        · exact fun i hi => hopen i (Finset.mem_insert_of_mem hi)
        · exact hsGood
        · exact hsMult
        · exact hn
      have hA : IsEmpty ↥(C a) ∨ ContractibleSpace ↥(C a) := by
        have h := hgood {a} (by simp) (Finset.singleton_nonempty a)
        have he : (⋂ i ∈ ({a} : Finset I), C i) = C a := by ext x; simp
        rw [he] at h
        exact h
      have hCa : Subsingleton (Homology ℚ (TopCat.of (C a)) (q + 1)) := by
        rcases hA with h | h
        · letI := h
          exact properCycle_empty_homology_subsingleton _ _
        · letI := h
          exact properCycle_contractible_homology_subsingleton _ _ (by omega)
      have hu : Subsingleton (Homology ℚ (TopCat.of U) (q + 1)) :=
        properCycle_homeomorph_homology_subsingleton
          (X := TopCat.of U) (Y := TopCat.of (C a))
          (properCycle_contained_subspace_homeomorph X (C a) T Set.subset_union_left) _ hCa
      have hv : Subsingleton (Homology ℚ (TopCat.of V) (q + 1)) :=
        properCycle_homeomorph_homology_subsingleton
          (X := TopCat.of V) (Y := TopCat.of S)
          (properCycle_contained_subspace_homeomorph X S T Set.subset_union_right) _ hS
      have hi : Subsingleton (Homology ℚ (TopCat.of ↥(U ∩ V)) q) := by
        cases d with
        | zero =>
          have hempty : IsEmpty ↥(U ∩ V) := by
            refine ⟨fun z => ?_⟩
            have hza : z.val.val ∈ C a := z.property.1
            have hzs : z.val.val ∈ S := z.property.2
            obtain ⟨i, his, hzi⟩ := Set.mem_iUnion₂.mp hzs
            have hai : a ≠ i := fun h => ha (h.symm ▸ his)
            have hpair : ({a, i} : Finset I) ⊆ insert a s := by
              intro j hj
              rcases Finset.mem_insert.mp hj with hj | hj
              · exact hj ▸ Finset.mem_insert_self a s
              · exact Finset.mem_insert_of_mem ((Finset.mem_singleton.mp hj) ▸ his)
            have hne : (⋂ j ∈ ({a, i} : Finset I), C j).Nonempty := by
              refine ⟨z.val.val, ?_⟩
              simp only [Set.mem_iInter]
              intro j hj
              rcases Finset.mem_insert.mp hj with hj | hj
              · exact hj ▸ hza
              · exact (Finset.mem_singleton.mp hj) ▸ hzi
            have hcard := hmult {a, i} hpair hne
            simp [hai] at hcard
          letI := hempty
          exact properCycle_empty_homology_subsingleton _ _
        | succ d =>
          let D : I → Set X := fun i => C a ∩ C i
          have hD : Subsingleton (Homology ℚ (TopCat.of ↥(⋃ i ∈ s, D i)) q) := by
            apply ih (d := d)
            · intro i hi
              exact (hopen a (Finset.mem_insert_self a s)).inter (hopen i (Finset.mem_insert_of_mem hi))
            · intro t ht htn
              change IsEmpty ↥(⋂ i ∈ t, C a ∩ C i) ∨ ContractibleSpace ↥(⋂ i ∈ t, C a ∩ C i)
              rw [properCycle_cover_intersection_adjoin C a t htn]
              exact hgood (insert a t) (Finset.insert_subset_insert a ht) (Finset.insert_nonempty a t)
            · exact properCycle_cover_overlap_card_bound C a s ha d hmult
            · omega
          have hDS : (⋃ i ∈ s, D i) = C a ∩ S := by
            ext x
            dsimp only [D, S]
            simp only [Set.mem_iUnion, Set.mem_inter_iff]
            constructor
            · rintro ⟨i, hi, hxA, hxi⟩
              exact ⟨hxA, ⟨i, hi, hxi⟩⟩
            · rintro ⟨hxA, i, hi, hxi⟩
              exact ⟨i, hi, hxA, hxi⟩
          let e := (properCycle_contained_subspace_homeomorph X (C a ∩ S) T
            (fun _ h => Or.inl h.1)).trans (Homeomorph.setCongr hDS).symm
          exact properCycle_homeomorph_homology_subsingleton
            (X := TopCat.of ↥(U ∩ V)) (Y := TopCat.of ↥(⋃ i ∈ s, D i)) e q hD
      exact properCycle_open_cover_homology_vanishes Z U V hUopen hVopen hcover q hu hv hi

end HodgeLean.Foundations.QuotientDuality
