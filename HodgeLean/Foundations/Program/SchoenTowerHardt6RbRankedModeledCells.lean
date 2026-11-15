import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedModeledCells
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRankEnumeration

/-! Ranked finite cell models give a global compatible homeomorphism with an actual Boolean graph. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ranked_modeled_cells {n : ℕ} {ι : Type*} [Fintype ι]
    (C T : ι → Set (EuclideanSpace ℝ (Fin n))) (D : ι → Finset ι) (rank : ι → ℕ)
    (hD : ∀ i j, j ∈ D i → rank j < rank i)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j ≠ i → rank j ≤ rank i → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i))
    (hTB : ∀ i, (⋃ j : D i, T j.val) ⊆ T i)
    (hTsep : ∀ i j, j ≠ i → rank j ≤ rank i → T j ∩ T i ⊆ ⋃ q : D i, T q.val)
    (model : ∀ i, C i ≃ₜ T i)
    (hmodel : ∀ i (x : C i), x.val ∉ intrinsicInterior ℝ (C i) ↔ (model i x).val ∈ ⋃ j : D i, T j.val)
    (F : ι → s2v_t11b_Formula n) (hF : ∀ i, (F i).realize = C i \ intrinsicInterior ℝ (C i))
    (J : ι → s2v_t11b_Formula (n + n))
    (hJ : ∀ i z, z ∈ (J i).realize ↔ ∃ x : C i,
      (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (model i x).val j)) :
    ∃ H : (⋃ i, C i) ≃ₜ (⋃ i, T i), ∃ G : s2v_t11b_Formula (n + n),
      (∀ i (x : (⋃ j, C j)), x.val ∈ C i ↔ (H x).val ∈ T i) ∧
      (∀ z, z ∈ G.realize ↔ ∃ x : (⋃ i, C i),
        (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (H x).val j)) := by
  classical
  obtain ⟨e, he⟩ := s2v_hardt6rb_rank_enumeration rank
  let D' : Fin (Fintype.card ι) → Finset (Fin (Fintype.card ι)) := fun i => (D (e i)).map e.symm.toEmbedding
  have hmem (i j : Fin (Fintype.card ι)) : j ∈ D' i ↔ e j ∈ D (e i) := by simp [D']
  have hD' : ∀ i j, j ∈ D' i → j.val < i.val := fun i j hj => he j i (hD (e i) (e j) ((hmem i j).mp hj))
  have hUnion (Q : ι → Set (EuclideanSpace ℝ (Fin n))) (i : Fin (Fintype.card ι)) :
      (⋃ j : D' i, Q (e j.val)) = ⋃ j : D (e i), Q j.val := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hx⟩
      exact ⟨⟨e j.val, (hmem i j.val).mp j.property⟩, hx⟩
    · rintro ⟨j, hx⟩
      exact ⟨⟨e.symm j.val, (hmem i _).mpr (by simpa only [e.apply_symm_apply] using j.property)⟩,
        by simpa only [e.apply_symm_apply] using hx⟩
  have horder (i j : Fin (Fintype.card ι)) (hji : j.val < i.val) : e j ≠ e i ∧ rank (e j) ≤ rank (e i) := by
    refine ⟨fun hij => (ne_of_lt hji) (congrArg Fin.val (e.injective hij)), ?_⟩
    by_contra hn
    exact lt_asymm hji (he i j (lt_of_not_ge hn))
  obtain ⟨H₀, G, hH₀, hG⟩ := s2v_hardt6rb_ordered_modeled_cells
    (fun i => C (e i)) (fun i => T (e i)) D' hD'
    (fun i => hcompact (e i)) (fun i => hconv (e i)) (fun i => hne (e i))
    (fun i => (hboundary (e i)).trans (hUnion C i).symm)
    (fun i j hji => hsep (e i) (e j) (horder i j hji).1 (horder i j hji).2)
    (fun i => by rw [hUnion T i]; exact hTB (e i))
    (fun i j hji => by rw [hUnion T i]; exact hTsep (e i) (e j) (horder i j hji).1 (horder i j hji).2)
    (fun i => model (e i)) (fun i x => by rw [hUnion T i]; exact hmodel (e i) x)
    (fun i => F (e i)) (fun i => hF (e i)) (fun i => J (e i)) (fun i => hJ (e i))
  have hAll (Q : ι → Set (EuclideanSpace ℝ (Fin n))) : (⋃ i, Q (e i)) = ⋃ i, Q i := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨e i, hi⟩,
      fun ⟨i, hi⟩ => ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩⟩
  let H := (Homeomorph.setCongr (hAll C)).symm.trans (H₀.trans (Homeomorph.setCongr (hAll T)))
  refine ⟨H, G, ?_, ?_⟩
  · intro i x
    have hh := hH₀ (e.symm i) ⟨x.val, (hAll C).symm ▸ x.property⟩
    change x.val ∈ C i ↔ (H₀ ⟨x.val, (hAll C).symm ▸ x.property⟩).val ∈ T i
    simpa only [e.apply_symm_apply] using hh
  · intro z
    rw [hG]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hAll C ▸ x.property⟩, hx, hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, (hAll C).symm ▸ x.property⟩, hx, hy⟩

end HodgeLean.Foundations.Program
