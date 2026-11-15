import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAdjoinModeledCell
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubmapCarrierPreimage

/-! Ordered compact convex cell models construct compatible global maps with actual Boolean graphs. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_modeled_cells {n N : ℕ}
    (C T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (D : Fin N → Finset (Fin N))
    (hD : ∀ i j, j ∈ D i → j.val < i.val)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j.val < i.val → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i))
    (hTB : ∀ i, (⋃ j : D i, T j.val) ⊆ T i)
    (hTsep : ∀ i j, j.val < i.val → T j ∩ T i ⊆ ⋃ q : D i, T q.val)
    (model : ∀ i, C i ≃ₜ T i)
    (hmodel : ∀ i (x : C i), x.val ∉ intrinsicInterior ℝ (C i) ↔ (model i x).val ∈ ⋃ j : D i, T j.val)
    (F : Fin N → s2v_t11b_Formula n) (hF : ∀ i, (F i).realize = C i \ intrinsicInterior ℝ (C i))
    (J : Fin N → s2v_t11b_Formula (n + n))
    (hJ : ∀ i z, z ∈ (J i).realize ↔ ∃ x : C i,
      (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (model i x).val j)) :
    ∃ H : (⋃ i, C i) ≃ₜ (⋃ i, T i), ∃ G : s2v_t11b_Formula (n + n),
      (∀ i (x : (⋃ j, C j)), x.val ∈ C i ↔ (H x).val ∈ T i) ∧
      (∀ z, z ∈ G.realize ↔ ∃ x : (⋃ i, C i),
        (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (H x).val j)) := by
  classical
  let U : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun k => {x | ∃ i, i.val < k ∧ x ∈ C i}
  let V : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun k => {x | ∃ i, i.val < k ∧ x ∈ T i}
  have prefix_succ (Q : Fin N → Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k < N) :
      {x | ∃ j, j.val < k ∧ x ∈ Q j} ∪ Q ⟨k, hk⟩ = {x | ∃ j, j.val < k + 1 ∧ x ∈ Q j} := by
    ext x
    constructor
    · rintro (⟨j, hj, hx⟩ | hx)
      · exact ⟨j, Nat.lt_succ_of_lt hj, hx⟩
      · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hx⟩
    · rintro ⟨j, hj, hx⟩
      by_cases he : j.val = k
      · right
        have hej : j = ⟨k, hk⟩ := Fin.ext he
        exact hej ▸ hx
      · exact Or.inl ⟨j, by omega, hx⟩
  have hprefix : ∀ k, k ≤ N → ∃ H : U k ≃ₜ V k, ∃ G : s2v_t11b_Formula (n + n),
      (∀ z, z ∈ G.realize ↔ ∃ x : U k,
        (∀ j, z (Fin.castAdd n j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (H x).val j)) ∧
      ∀ i (hi : i.val < k), ∃ e : C i ≃ₜ T i, ∀ x : C i,
        (H ⟨x.val, ⟨i, hi, x.property⟩⟩).val = (e x).val := by
    intro k
    induction k with
    | zero =>
      intro _
      have he : U 0 = V 0 := by ext x; simp [U, V]
      let H := Homeomorph.setCongr he
      refine ⟨H, .compl (.nonneg 0), ?_, ?_⟩
      · intro z
        constructor
        · intro hz
          simpa only [s2v_t11b_Formula.realize, Set.mem_compl_iff, Set.mem_setOf_eq, map_zero,
            le_refl, not_true_eq_false] using hz
        · rintro ⟨x, _, _⟩
          obtain ⟨i, hi, _⟩ := x.property
          omega
      · intro i hi
        omega
    | succ k ih =>
      intro hkN
      obtain ⟨H, G, hG, hprev⟩ := ih (Nat.le_of_succ_le hkN)
      have hk : k < N := lt_of_lt_of_le (Nat.lt_succ_self k) hkN
      let i : Fin N := ⟨k, hk⟩
      let S := ⋃ j : D i, T j.val
      have hCA : C i \ intrinsicInterior ℝ (C i) ⊆ U k := by
        intro x hx
        rw [hboundary i] at hx
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact ⟨j.val, hD i j.val j.property, hj⟩
      have hSB : S ⊆ V k := by
        intro x hx
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact ⟨j.val, hD i j.val j.property, hj⟩
      have hcell (j : D i) (x : U k) : x.val ∈ C j.val ↔ (H x).val ∈ T j.val := by
        obtain ⟨e, he⟩ := hprev j.val (hD i j.val j.property)
        exact s2v_hardt6rb_submap_carrier_preimage (U k) (C j.val) (V k) (T j.val)
          (fun y hy => ⟨j.val, hD i j.val j.property, hy⟩) H e he x
      have hmem (x : U k) : x.val ∈ C i \ intrinsicInterior ℝ (C i) ↔ (H x).val ∈ S := by
        rw [hboundary i]
        simp only [S, Set.mem_iUnion]
        exact exists_congr (fun j => hcell j x)
      have hAC : U k ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i) := by
        rintro x ⟨⟨j, hj, hxj⟩, hxi⟩
        exact hsep i j hj ⟨hxj, hxi⟩
      have hBT : V k ∩ T i ⊆ S := by
        rintro x ⟨⟨j, hj, hxj⟩, hxi⟩
        exact hTsep i j hj ⟨hxj, hxi⟩
      have hUk : IsCompact (U k) := by
        have hu : U k = ⋃ j : {j : Fin N // j.val < k}, C j.val := by
          ext x
          simp only [U, Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
        rw [hu]
        exact isCompact_iUnion (fun j => hcompact j.val)
      obtain ⟨H', G', hOld, ⟨e, hNew⟩, hG'⟩ := s2v_hardt6rb_adjoin_modeled_cell (U k) (C i) (V k)
        (T i) S hUk (hcompact i) (hconv i) (hne i) hCA hSB (hTB i) hAC hBT H hmem
        (model i) (hmodel i) (F i) (hF i) G (J i) hG (hJ i)
      have hU : U k ∪ C i = U (k + 1) := prefix_succ C k hk
      have hV : V k ∪ T i = V (k + 1) := prefix_succ T k hk
      let Hnew := (Homeomorph.setCongr hU).symm.trans (H'.trans (Homeomorph.setCongr hV))
      refine ⟨Hnew, G', ?_, ?_⟩
      · intro z
        rw [hG']
        constructor
        · rintro ⟨x, hx, hy⟩
          exact ⟨⟨x.val, hU ▸ x.property⟩, hx, hy⟩
        · rintro ⟨x, hx, hy⟩
          exact ⟨⟨x.val, hU.symm ▸ x.property⟩, hx, hy⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          exact ⟨e, hNew⟩
        · have hjk : j.val < k := by
            have hne : j.val ≠ k := fun h => hji (Fin.ext h)
            omega
          obtain ⟨ej, hej⟩ := hprev j hjk
          refine ⟨ej, fun x => ?_⟩
          exact (hOld ⟨x.val, ⟨j, hjk, x.property⟩⟩).trans (hej x)
  obtain ⟨H, G, hG, hmaps⟩ := hprefix N le_rfl
  have hU : U N = ⋃ i, C i := by
    ext x
    simp only [U, Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.isLt, hi⟩⟩
  have hV : V N = ⋃ i, T i := by
    ext x
    simp only [V, Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.isLt, hi⟩⟩
  let Hfinal := (Homeomorph.setCongr hU).symm.trans (H.trans (Homeomorph.setCongr hV))
  refine ⟨Hfinal, G, ?_, ?_⟩
  · intro i x
    obtain ⟨e, he⟩ := hmaps i i.isLt
    exact s2v_hardt6rb_submap_carrier_preimage (U N) (C i) (V N) (T i)
      (fun y hy => ⟨i, i.isLt, hy⟩) H e he ⟨x.val, hU.symm ▸ x.property⟩
  · intro z
    rw [hG]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hU ▸ x.property⟩, hx, hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hU.symm ▸ x.property⟩, hx, hy⟩

end HodgeLean.Foundations.Program
