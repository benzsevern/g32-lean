import HodgeLean.Foundations.Program.SchoenTowerHardtCad6Join

/-! Implication from Boolean chart partitions and dimension extraction to descending
frontier refinement. Local triviality is outside this interface.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad6_layer_aux {n d k l : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hP : ∀ i, P.dim i ≤ d)
    (B : Fin k → s2v_t11b_Formula n) (L : Fin l → s2v_t11b_Formula n) :
    ∃ U T : s2v_t11b_Formula n,
    ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ PT : s2v_hardt_cad5_Partition T.realize,
    ∃ boundary limits : Fin PU.count → s2v_t11b_Formula n,
    ∃ remainderMarks : Fin (k + l) → s2v_t11b_Formula n,
      U.realize ⊆ S.realize ∧ T.realize = S.realize \ U.realize ∧
      PT.dimension < (d : ℤ) ∧
      (∀ i, PU.dim i = d) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      (∀ i, (boundary i).realize = closure (PU.cell i).realize \ (PU.cell i).realize) ∧
      (∀ i, (limits i).realize = closure (PU.cell i).realize) ∧
      (∀ i j, (PU.cell i).realize ⊆ (B j).realize ∨
        Disjoint (PU.cell i).realize (B j).realize) ∧
      (∀ i j, (PU.cell i).realize ⊆ (L j).realize ∨
        Disjoint (PU.cell i).realize (L j).realize) ∧
      (∀ j, (remainderMarks (Fin.castAdd l j)).realize = T.realize ∩ (B j).realize) ∧
      (∀ j, (remainderMarks (Fin.natAdd k j)).realize = T.realize ∩ (L j).realize) := by
  classical
  let marks : Fin (k + l) → s2v_t11b_Formula n := Fin.addCases B L
  have restrictions (T : s2v_t11b_Formula n) :
      ∃ M : Fin (k + l) → s2v_t11b_Formula n,
        (∀ j, (M (Fin.castAdd l j)).realize = T.realize ∩ (B j).realize) ∧
        (∀ j, (M (Fin.natAdd k j)).realize = T.realize ∩ (L j).realize) := by
    exact ⟨fun j => .inter T (marks j), by simp [marks, s2v_t11b_Formula.realize], by simp [marks, s2v_t11b_Formula.realize]⟩
  have hdim : P.dimension ≤ (d : ℤ) :=
    s2v_hardt_cad5_max_le P.dim d (by omega) (fun i => by exact_mod_cast hP i)
  by_cases hlt : P.dimension < (d : ℤ)
  · let E : s2v_t11b_Formula n := .compl (.nonneg 0)
    obtain ⟨PE⟩ := s2v_hardt_cad5_partition_exists E
    have he : E.realize = ∅ := by ext x; simp [E, s2v_t11b_Formula.realize]
    have hz := (s2v_hardt_cad5_count_eq_zero_iff PE).mpr he
    have no (i : Fin PE.count) : False := by have := i.isLt; omega
    obtain ⟨M, hM, hN⟩ := restrictions S
    refine ⟨E, S, PE, P, (fun i => (no i).elim), (fun i => (no i).elim), M,
      ?_, ?_, hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hM, hN⟩
    · rw [he]; exact Set.empty_subset _
    · rw [he, Set.sdiff_empty]
    all_goals intro i; exact (no i).elim
  · have heq : P.dimension = (d : ℤ) := by omega
    obtain ⟨R, ha⟩ := s2v_hardt_cad6_adapt S marks
    have hr : R.dimension = (d : ℤ) :=
      (s2v_hardt_cad5_invariance S S R P P).1.trans heq
    have hs : S.realize.Nonempty := by
      by_contra h
      have := s2v_hardt_cad5_dimension_empty P (Set.not_nonempty_iff_eq_empty.mp h)
      omega
    obtain ⟨Z, PZ, U, PU, T, PT, parent, _, _, hu, hp, ho, _, hd, ht, hsmall, _⟩ :=
      s2v_hardt_cad5_partition_top S R
    choose C hC hrest using fun i => s2v_hardt2_closure_formula (PU.cell i)
    let boundary : Fin PU.count → s2v_t11b_Formula n :=
      fun i => .inter (C i) (.compl (PU.cell i))
    obtain ⟨M, hM, hN⟩ := restrictions T
    have hsub (i) : (PU.cell i).realize ⊆ (R.cell (parent i)).realize :=
      fun _ hx => (hp i hx).1
    have had (i) (j) : (PU.cell i).realize ⊆ (marks j).realize ∨
        Disjoint (PU.cell i).realize (marks j).realize := by
      rcases ha (parent i) j with h | h
      · exact Or.inl (fun _ hx => h (hsub i hx))
      · exact Or.inr (h.mono_left (hsub i))
    refine ⟨U, T, PU, PT, boundary, C, M, ?_, ht, ?_, ?_, ho, hd, ?_, hC,
      ?_, ?_, hM, hN⟩
    · intro x hx
      rw [← PU.cover] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact s2v_hardt_cad6_cell_subset R (parent i) (hsub i hi)
    · simpa [hr] using hsmall hs
    · intro i
      have := (hu i).1
      rw [hr] at this
      exact_mod_cast this
    · intro i
      change (C i).realize ∩ (PU.cell i).realizeᶜ = _
      rw [hC i]; rfl
    · intro i j
      simpa [marks] using had i (Fin.castAdd l j)
    · intro i j
      simpa [marks] using had i (Fin.natAdd k j)


theorem s2v_hardt_cad6_descending_aux {n d k : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hP : ∀ i, P.dim i ≤ d)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ Q : s2v_hardt_cad5_Partition S.realize,
      (∀ i, Q.dim i ≤ d) ∧
      (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨
        Disjoint (Q.cell i).realize (B j).realize) ∧
      (∀ i j, ((Q.cell j).realize ∩ closure (Q.cell i).realize).Nonempty →
        (Q.cell j).realize ⊆ closure (Q.cell i).realize ∧
          (j = i ∨ Q.dim j < Q.dim i)) := by
  classical
  induction d using Nat.strong_induction_on generalizing k S with
  | h d ih =>
    obtain ⟨U, T, PU, PT, bd, lim, rm, hUS, hT, hsmall, hdim, hopen,
      hsep, hbd, hlim, hadapt, _, _, _⟩ :=
      s2v_hardt_cad6_layer_aux S P hP B (Fin.elim0 : Fin 0 → _)
    let marks : Fin (k + PU.count) → s2v_t11b_Formula n := Fin.addCases B lim
    have lower : ∃ R : s2v_hardt_cad5_Partition T.realize,
        (∀ i, R.dim i < d) ∧
        (∀ i j, (R.cell i).realize ⊆ (marks j).realize ∨
          Disjoint (R.cell i).realize (marks j).realize) ∧
        (∀ i j, ((R.cell j).realize ∩ closure (R.cell i).realize).Nonempty →
          (R.cell j).realize ⊆ closure (R.cell i).realize ∧
            (j = i ∨ R.dim j < R.dim i)) := by
      by_cases hz : d = 0
      · have no (i : Fin PT.count) : False := by
          have hle : (PT.dim i : ℤ) ≤ PT.dimension := s2v_hardt_cad5_le_max PT.dim i
          omega
        refine ⟨PT, ?_, ?_, ?_⟩
        all_goals intro i; exact (no i).elim
      · have hb (i : Fin PT.count) : PT.dim i ≤ d - 1 := by
          have hle : (PT.dim i : ℤ) ≤ PT.dimension := s2v_hardt_cad5_le_max PT.dim i
          omega
        obtain ⟨R, hr, ha, hi⟩ := ih (d - 1) (by omega) T PT hb marks
        exact ⟨R, fun i => by have := hr i; omega, ha, hi⟩
    obtain ⟨R, hr, ha, hi⟩ := lower
    have hUT : Disjoint U.realize T.realize := by rw [hT]; exact Set.disjoint_sdiff_right
    have hcover : U.realize ∪ T.realize = S.realize := by
      rw [hT]; exact Set.union_sdiff_cancel hUS
    let Q := s2v_hardt_cad6_join PU R hUT hcover
    have hrev (a : Fin PU.count) (b : Fin R.count) :
        Disjoint (PU.cell a).realize (closure (R.cell b).realize) := by
      apply s2v_hardt_cad6_no_reverse
        ((s2v_hardt_cad6_cell_subset PU a).trans hUS) _ (hopen a)
      intro x hx
      have ht := s2v_hardt_cad6_cell_subset R b hx
      rw [hT] at ht
      exact ⟨ht.1, fun hc => ht.2 (s2v_hardt_cad6_cell_subset PU a hc)⟩
    refine ⟨Q, ?_, ?_, ?_⟩
    · exact Fin.addCases (fun i => by simp [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry, hdim i])
        (fun i => by simpa [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry] using (hr i).le)
    · intro i j
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · simpa [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry] using hadapt a j
      · simpa [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry, marks] using ha a (Fin.castAdd PU.count j)
    · intro i j
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
        refine Fin.addCases (fun b => ?_) (fun b => ?_) j
      · simp only [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry, Fin.addCases_left]
        intro hn
        by_cases he : b = a
        · subst b; exact ⟨subset_closure, Or.inl rfl⟩
        · obtain ⟨x, hx, hy⟩ := hn
          exact False.elim (Set.disjoint_left.mp (hsep a b (Ne.symm he)) hx hy)
      · simp only [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry, Fin.addCases_left, Fin.addCases_right]
        intro hn
        have ha' := ha b (Fin.natAdd k a)
        simp only [marks, Fin.addCases_right, hlim] at ha'
        rcases ha' with hh | hh
        · exact ⟨hh, Or.inr (by rw [hdim a]; exact hr b)⟩
        · obtain ⟨x, hx, hy⟩ := hn
          exact False.elim (Set.disjoint_left.mp hh hx hy)
      · simp only [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry, Fin.addCases_left, Fin.addCases_right]
        rintro ⟨x, hx, hy⟩
        exact False.elim (Set.disjoint_left.mp (hrev b a) hx hy)
      · simp only [Q, s2v_hardt_cad6_join, s2v_hardt_cad6_entry, Fin.addCases_right]
        intro hn
        obtain ⟨hs, he | he⟩ := hi a b hn
        · exact ⟨hs, Or.inl (congrArg (Fin.natAdd PU.count) he)⟩
        · exact ⟨hs, Or.inr he⟩


theorem s2v_hardt_cad6_carrier_aux {n k : ℕ} (A : s2v_t11b_Formula n)
    (B : Fin k → s2v_t11b_Formula n) :
    ∃ P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
    ∃ Q : s2v_hardt_cad5_Partition A.realize,
    ∃ select : Fin Q.count ↪ Fin P.count,
      (∀ i, Q.cell i = P.cell (select i) ∧ Q.dim i = P.dim (select i)) ∧
      (∀ j, (P.cell j).realize ⊆ A.realize ↔ ∃ i, select i = j) ∧
      (∀ i, (P.cell i).realize ⊆ A.realize ∨ Disjoint (P.cell i).realize A.realize) ∧
      (∀ i j, (P.cell i).realize ⊆ (B j).realize ∨
        Disjoint (P.cell i).realize (B j).realize) ∧
      (∀ i j, ((P.cell j).realize ∩ closure (P.cell i).realize).Nonempty →
        (P.cell j).realize ⊆ closure (P.cell i).realize ∧
          (j = i ∨ P.dim j < P.dim i)) ∧
      (∀ i j, (Q.cell i).realize ⊆ (B j).realize ∨
        Disjoint (Q.cell i).realize (B j).realize) ∧
      (∀ i j, ((Q.cell j).realize ∩ closure (Q.cell i).realize).Nonempty →
        (Q.cell j).realize ⊆ closure (Q.cell i).realize ∧
          (j = i ∨ Q.dim j < Q.dim i)) := by
  classical
  let S : s2v_t11b_Formula n := .nonneg 0
  obtain ⟨R, _⟩ := s2v_hardt_cad6_adapt S (Fin.elim0 : Fin 0 → _)
  have hdesc := s2v_hardt_cad6_descending_aux S R R.bound (Fin.cases A B)
  have hS : S.realize = Set.univ := by ext x; simp [S, s2v_t11b_Formula.realize]
  rw [hS] at hdesc
  obtain ⟨P, _, ha, hi⟩ := hdesc
  have hA (i) : (P.cell i).realize ⊆ A.realize ∨
      Disjoint (P.cell i).realize A.realize := ha i 0
  obtain ⟨Q, p, hp, hc, hd, _⟩ := s2v_hardt_cad5_select P (Set.subset_univ _) hA
  let select : Fin Q.count ↪ Fin P.count := ⟨p, hp⟩
  have hB (i) (j) : (P.cell i).realize ⊆ (B j).realize ∨
      Disjoint (P.cell i).realize (B j).realize := ha i j.succ
  refine ⟨P, Q, select, fun i => ⟨hc i, hd i⟩, ?_, hA, hB, hi, ?_, ?_⟩
  · intro j
    constructor
    · intro hj
      obtain ⟨x, hx⟩ := P.nonempty j
      have hxA := hj hx
      rw [← Q.cover] at hxA
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxA
      rw [hc i] at hi
      refine ⟨i, ?_⟩
      by_contra hn
      exact Set.disjoint_left.mp (P.disjoint hn) hi hx
    · rintro ⟨i, rfl⟩
      change (P.cell (p i)).realize ⊆ A.realize
      rw [← hc i]
      exact s2v_hardt_cad6_cell_subset Q i
  · intro i j
    rw [hc i]
    exact hB (p i) j
  · intro i j hn
    rw [hc j, hc i] at hn ⊢
    obtain ⟨hs, he | he⟩ := hi (p i) (p j) hn
    · exact ⟨hs, Or.inl (hp he)⟩
    · exact ⟨hs, Or.inr (by simpa [hd i, hd j] using he)⟩


end HodgeLean.Foundations.Program
