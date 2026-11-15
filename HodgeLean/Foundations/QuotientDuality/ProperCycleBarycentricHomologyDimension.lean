import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricGoodCover

/-! # Ordinary homology dimension of actual finite barycentric face carriers -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual finite barycentric carriers with face cardinality at most d+1 have zero ordinary rational homology above d, using their original positive-coordinate open stars.
Source: Hatcher, Algebraic Topology, sections 2.1, 2.2 and 4G; Munkres, Elements of Algebraic Topology, section 2.
HC no distance; AV milestone no distance. -/
lemma properCycle_barycentric_carrier_homology_vanishes
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : Set (Finset ι))
    (d : ℕ) (hbound : ∀ s ∈ F, s.card ≤ d + 1) (n : ℕ) (hn : d < n) :
    Subsingleton (Homology ℚ
      (TopCat.of {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0}) n) := by
  let Y := TopCat.of {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0}
  let C : ι → Set Y := fun i => {w | 0 < w.val.val i}
  have hcover : (⋃ i ∈ (Finset.univ : Finset ι), C i) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro w
    have hp : ∃ i, 0 < w.val.val i := by
      by_contra! h
      have hz : ∀ i, w.val.val i = 0 := fun i => le_antisymm (h i) (w.val.property.1 i)
      have hh := w.val.property.2
      simp only [hz, Finset.sum_const_zero] at hh
      exact zero_ne_one hh
    obtain ⟨i, hi⟩ := hp
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hopen : ∀ i ∈ (Finset.univ : Finset ι), IsOpen (C i) := by
    intro i _
    exact isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
  have hgood : ∀ t : Finset ι, t ⊆ Finset.univ → t.Nonempty →
      IsEmpty ↥(⋂ i ∈ t, C i) ∨ ContractibleSpace ↥(⋂ i ∈ t, C i) := by
    intro t _ ht
    have he : (⋂ i ∈ t, C i) = {w : Y | ∀ i ∈ t, 0 < w.val.val i} := by
      ext w
      simp only [Set.mem_iInter]
      rfl
    by_cases hne : Nonempty ↥(⋂ i ∈ t, C i)
    · right
      rw [he] at hne ⊢
      exact properCycle_barycentric_star_contractible F t ht hne
    · exact Or.inl (not_nonempty_iff.mp hne)
  have hmult : ∀ t : Finset ι, t ⊆ Finset.univ → (⋂ i ∈ t, C i).Nonempty → t.card ≤ d + 1 := by
    intro t _ ht
    obtain ⟨w, hw⟩ := ht
    obtain ⟨s, hs, hws⟩ := w.property
    have hts : t ⊆ s := by
      intro i hi
      by_contra his
      have hp : 0 < w.val.val i := Set.mem_iInter.mp (Set.mem_iInter.mp hw i) hi
      rw [hws i his] at hp
      exact (lt_irrefl 0) hp
    exact (Finset.card_le_card hts).trans (hbound s hs)
  have h := properCycle_finite_good_cover_homology_vanishes Y C Finset.univ d hopen hgood hmult n hn
  rw [hcover] at h
  exact properCycle_homeomorph_homology_subsingleton
    (X := Y) (Y := TopCat.of ↥(Set.univ : Set Y)) (Homeomorph.Set.univ Y).symm n h

end HodgeLean.Foundations.QuotientDuality
