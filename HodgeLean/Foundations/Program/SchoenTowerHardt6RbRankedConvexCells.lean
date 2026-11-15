import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedConvexCells
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRankEnumeration

/-! Finite ranked convex cell families construct a common actual geometric triangulation without an imposed enumeration. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ranked_convex_cells {E ι : Type*} [DecidableEq E] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : ι → Set E) (D : ι → Finset ι) (rank : ι → ℕ)
    (hD : ∀ i j, j ∈ D i → rank j < rank i)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i))
    (a : ι → E) (ha : ∀ i, a i ∈ intrinsicInterior ℝ (C i))
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j ≠ i → rank j ≤ rank i → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i))
    (hcase : ∀ i, (∃ p, C i = {p}) ∨ (C i \ intrinsicInterior ℝ (C i)).Nonempty) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = ⋃ i, C i ∧
      ∀ i, ∃ P : Geometry.SimplicialComplex ℝ E,
        P.faces.Finite ∧ P.space = C i ∧ P.faces ⊆ K.faces := by
  classical
  obtain ⟨e, he⟩ := s2v_hardt6rb_rank_enumeration rank
  let D' : Fin (Fintype.card ι) → Finset (Fin (Fintype.card ι)) :=
    fun i => (D (e i)).map e.symm.toEmbedding
  have hmem (i j : Fin (Fintype.card ι)) : j ∈ D' i ↔ e j ∈ D (e i) := by
    simp [D']
  have hD' : ∀ i j, j ∈ D' i → j.val < i.val := by
    intro i j hj
    exact he j i (hD (e i) (e j) ((hmem i j).mp hj))
  have hb' (i : Fin (Fintype.card ι)) :
      C (e i) \ intrinsicInterior ℝ (C (e i)) = ⋃ j : D' i, C (e j.val) := by
    rw [hboundary (e i)]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hx⟩
      exact ⟨⟨e.symm j.val, (hmem i _).mpr (by simpa only [e.apply_symm_apply] using j.property)⟩,
        by simpa only [e.apply_symm_apply] using hx⟩
    · rintro ⟨j, hx⟩
      exact ⟨⟨e j.val, (hmem i j.val).mp j.property⟩, hx⟩
  have hs' : ∀ i j : Fin (Fintype.card ι), j.val < i.val →
      C (e j) ∩ C (e i) ⊆ C (e i) \ intrinsicInterior ℝ (C (e i)) := by
    intro i j hji
    apply hsep (e i) (e j)
    · exact fun hij => (ne_of_lt hji) (congrArg Fin.val (e.injective hij))
    · by_contra hn
      have hh := he i j (lt_of_not_ge hn)
      exact (lt_asymm hji hh)
  obtain ⟨K, hK, hKs, hP⟩ := s2v_hardt6rb_ordered_convex_cells
    (fun i => C (e i)) D' hD' (fun i => hcompact (e i)) (fun i => hconv (e i))
    (fun i => a (e i)) (fun i => ha (e i)) hb' hs' (fun i => hcase (e i))
  refine ⟨K, hK, ?_, ?_⟩
  · rw [hKs]
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨e i, hi⟩,
      fun ⟨i, hi⟩ => ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩⟩
  · intro i
    simpa only [e.apply_symm_apply] using hP (e.symm i)

end HodgeLean.Foundations.Program
