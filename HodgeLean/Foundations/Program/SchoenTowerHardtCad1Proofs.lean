import HodgeLean.Foundations.Program.SchoenTowerHardtCad1Geometry

/-! One-variable cut geometry for the CAD construction. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad1_cut_cells_aux (R : Finset ℝ) :
    ∃ c : Fin (2 * R.card + 1) → s2v_t11b_Formula 1,
    ∃ dim : Fin (2 * R.card + 1) → ℕ,
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i, dim i ≤ 1) ∧
      (∀ i, Nonempty ((c i).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin (dim i)) | ∀ a, -1 < t a ∧ t a < 1})) ∧
      (∀ i, (dim i = 0 ↔ ∃ r ∈ R,
        (c i).realize = {x : EuclideanSpace ℝ (Fin 1) | x 0 = r})) ∧
      (∀ i, dim i = 1 → IsOpen (c i).realize ∧
        Set.OrdConnected {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize} ∧
        ∀ x ∈ (c i).realize, x 0 ∉ R) ∧
      (∀ i (x y : EuclideanSpace ℝ (Fin 1)), x ∈ (c i).realize →
        y ∈ (c i).realize → ∀ r ∈ R,
          (x 0 ≤ r ↔ y 0 ≤ r) ∧ (r ≤ x 0 ↔ r ≤ y 0)) ∧
      (∀ i j, ((c j).realize ∩ closure (c i).realize).Nonempty →
        (c j).realize ⊆ closure (c i).realize ∧ (j = i ∨ dim j < dim i)) := by
  classical
  let n := R.card
  let d : Fin n ↪o ℝ := R.orderEmbOfFin rfl
  have hd : StrictMono d := d.strictMono
  have dr : ∀ r, r ∈ R ↔ ∃ k, d k = r := by
    intro r
    change r ∈ (R : Set ℝ) ↔ _
    rw [← Finset.range_orderEmbOfFin R rfl]
    rfl
  choose g hg using s2v_cad1_gap_formula (fun k => d k)
  let p : Fin n → s2v_t11b_Formula 1 := fun k =>
    .inter (.nonneg (MvPolynomial.X 0 - MvPolynomial.C (d k)))
      (.nonneg (MvPolynomial.C (d k) - MvPolynomial.X 0))
  have hp : ∀ k x, x ∈ (p k).realize ↔ x 0 = d k := by
    intro k x
    simp [p, s2v_t11b_Formula.realize, le_antisymm_iff, and_comm]
  let C : Fin n ⊕ Fin (n + 1) → s2v_t11b_Formula 1 := Sum.elim p g
  let D : Fin n ⊕ Fin (n + 1) → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  let e : Fin (2 * R.card + 1) ≃ (Fin n ⊕ Fin (n + 1)) :=
    Fintype.equivOfCardEq (by simp [n]; omega)
  have pt (r : ℝ) : {x : EuclideanSpace ℝ (Fin 1) | x 0 = r} =
      {s2v_cad1_coord.symm r} := by
    ext x
    change s2v_cad1_coord x = r ↔ x = s2v_cad1_coord.symm r
    exact s2v_cad1_coord.eq_symm_apply.symm
  have pne (k : Fin n) : (p k).realize.Nonempty :=
    ⟨s2v_cad1_coord.symm (d k), (hp _ _).mpr (s2v_cad1_coord.apply_symm_apply _)⟩
  have gne (i : Fin (n + 1)) : (g i).realize.Nonempty := by
    obtain ⟨t, ht⟩ := (s2v_cad1_gap_geometry (fun k => d k) hd i).1
    exact ⟨s2v_cad1_coord.symm t, (hg _ _).mpr ht⟩
  have avoid (i : Fin (n + 1)) (x) (hx : x ∈ (g i).realize) (k : Fin n) :
      x 0 ≠ d k := by
    have h := (hg i x).mp hx k
    by_cases hk : k.val < i.val
    · exact ne_of_gt (h.1 hk)
    · exact ne_of_lt (h.2 (by omega))
  have gsep (i j : Fin (n + 1)) (hij : i < j) (x)
      (hx : x ∈ (g i).realize) (hy : x ∈ closure (g j).realize) : False := by
    let k : Fin n := ⟨i.val, by have := j.isLt; change i.val < j.val at hij; omega⟩
    have hxi := ((hg i x).mp hx k).2 (by rfl)
    have hsub : (g j).realize ⊆ {y | d k ≤ y 0} := by
      intro y hy
      exact le_of_lt (((hg j y).mp hy k).1 hij)
    have hyi : d k ≤ x 0 := closure_minimal hsub
      (isClosed_le continuous_const s2v_cad1_coord.continuous) hy
    exact (not_lt_of_ge hyi) hxi
  have gsep' (i j : Fin (n + 1)) (hji : j < i) (x)
      (hx : x ∈ (g i).realize) (hy : x ∈ closure (g j).realize) : False := by
    let k : Fin n := ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
    have hxi := ((hg i x).mp hx k).1 hji
    have hsub : (g j).realize ⊆ {y | y 0 ≤ d k} := by
      intro y hy
      exact le_of_lt (((hg j y).mp hy k).2 (by rfl))
    have hyi : x 0 ≤ d k := closure_minimal hsub
      (isClosed_le s2v_cad1_coord.continuous continuous_const) hy
    exact (not_lt_of_ge hyi) hxi
  have pset (k : Fin n) : (p k).realize = {s2v_cad1_coord.symm (d k)} := by
    ext x
    rw [← pt]
    exact hp k x
  have disj : Pairwise (fun i j => Disjoint (C i).realize (C j).realize) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    cases i with
    | inl k =>
      cases j with
      | inl l =>
        exact hij (congrArg Sum.inl (d.injective ((hp k x).mp hx |>.symm.trans ((hp l x).mp hy))))
      | inr l => exact avoid l x hy k ((hp k x).mp hx)
    | inr k =>
      cases j with
      | inl l => exact avoid k x hx l ((hp l x).mp hy)
      | inr l =>
        rcases lt_or_gt_of_ne (fun h => hij (congrArg Sum.inr h)) with h | h
        · exact gsep k l h x hx (subset_closure hy)
        · exact gsep' k l h x hx (subset_closure hy)
  have cover (x : EuclideanSpace ℝ (Fin 1)) : ∃ i, x ∈ (C i).realize := by
    by_cases h : ∃ k, x 0 = d k
    · obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inl k, (hp k x).mpr hk⟩
    have hne : ∀ k, x 0 ≠ d k := by simpa using h
    let U := Finset.univ.filter (fun k : Fin n => x 0 < d k)
    by_cases hu : U.Nonempty
    · let k := U.min' hu
      have hk : x 0 < d k := (Finset.mem_filter.mp (Finset.min'_mem U hu)).2
      refine ⟨Sum.inr k.castSucc, (hg _ _).mpr ?_⟩
      intro l
      constructor
      · intro hl
        have hnot : ¬ x 0 < d l := by
          intro ht
          have hkl := Finset.min'_le U l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
          exact not_le_of_gt hl hkl
        exact lt_of_le_of_ne (le_of_not_gt hnot) (hne l).symm
      · intro hl
        exact lt_of_lt_of_le hk (hd.monotone hl)
    · refine ⟨Sum.inr (Fin.last n), (hg _ _).mpr ?_⟩
      intro k
      constructor
      · intro _
        have hnot : ¬ x 0 < d k := by
          intro ht
          exact hu ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
        exact lt_of_le_of_ne (le_of_not_gt hnot) (hne k).symm
      · intro hk
        have := k.isLt
        simp only [Fin.val_last] at hk
        omega
  refine ⟨fun i => C (e i), fun i => D (e i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases he : e i with
    | inl k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      exact pne k
    | inr k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      exact gne k
  · intro i j hij
    exact disj (fun h => hij (e.injective h))
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := cover x
    exact ⟨e.symm i, by simpa using hi⟩
  · intro i
    cases he : e i <;> simp [he, D]
  · intro i
    suffices hh : ∀ q, Nonempty ((C q).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin (D q)) | ∀ a, -1 < t a ∧ t a < 1}) from hh (e i)
    intro q
    cases q with
    | inl k =>
      change Nonempty ((p k).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin 0) | ∀ a, -1 < t a ∧ t a < 1})
      rw [pset]
      letI : Unique {t : EuclideanSpace ℝ (Fin 0) | ∀ a, -1 < t a ∧ t a < 1} :=
        uniqueOfSubsingleton ⟨0, fun a => Fin.elim0 a⟩
      exact ⟨Homeomorph.homeomorphOfUnique _ _⟩
    | inr k =>
      change Nonempty ((g k).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin 1) | ∀ a, -1 < t a ∧ t a < 1})
      let a : (g k).realize ≃ₜ s2v_cad1_gap (fun k => d k) k :=
        s2v_cad1_coord.subtype (hg k)
      let b : {t : EuclideanSpace ℝ (Fin 1) | ∀ a, -1 < t a ∧ t a < 1} ≃ₜ
          Set.Ioo (-1 : ℝ) 1 := s2v_cad1_coord.subtype (by
        intro x
        exact ⟨fun h => h 0, fun h a => by fin_cases a; exact h⟩)
      exact ⟨(a.trans (Classical.choice
        (s2v_cad1_gap_geometry (fun k => d k) hd k).2.2.2)).trans b.symm⟩
  · intro i
    cases he : e i with
    | inl k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      refine ⟨fun _ => ⟨d k, (dr _).mpr ⟨k, rfl⟩, ?_⟩, fun _ => True.intro⟩
      ext x
      exact hp k x
    | inr k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      change (1 = 0 ↔ ∃ r ∈ R, (g k).realize = {x | x 0 = r})
      constructor
      · norm_num
      · rintro ⟨r, hr, hh⟩
        obtain ⟨l, rfl⟩ := (dr r).mp hr
        obtain ⟨x, hx⟩ := gne k
        exact False.elim (avoid k x hx l (by rw [hh] at hx; exact hx))
  · intro i hi
    cases he : e i with
    | inl k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      simp [D] at hi
    | inr k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      change IsOpen (g k).realize ∧ _
      have heq : (g k).realize = s2v_cad1_coord ⁻¹' s2v_cad1_gap (fun k => d k) k :=
        Set.ext (hg k)
      refine ⟨heq ▸ (s2v_cad1_gap_geometry (fun k => d k) hd k).2.1.preimage
        s2v_cad1_coord.continuous, ?_, ?_⟩
      · convert (s2v_cad1_gap_geometry (fun k => d k) hd k).2.2.1 using 1
        ext t
        exact hg k _
      · intro x hx hr
        obtain ⟨l, hl⟩ := (dr _).mp hr
        exact avoid k x hx l hl.symm
  · intro i x y hx hy r hr
    obtain ⟨l, rfl⟩ := (dr r).mp hr
    cases he : e i with
    | inl k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      rw [(hp k x).mp hx, (hp k y).mp hy]
      exact ⟨Iff.rfl, Iff.rfl⟩
    | inr k =>
      simp only [he, C, D, Sum.elim_inl, Sum.elim_inr] at *
      have hxx := (hg k x).mp hx l
      have hyy := (hg k y).mp hy l
      by_cases hl : l.val < k.val
      · have h1 := hxx.1 hl
        have h2 := hyy.1 hl
        exact ⟨iff_of_false (not_le_of_gt h1) (not_le_of_gt h2),
          iff_of_true h1.le h2.le⟩
      · have h1 := hxx.2 (by omega)
        have h2 := hyy.2 (by omega)
        exact ⟨iff_of_true h1.le h2.le,
          iff_of_false (not_le_of_gt h1) (not_le_of_gt h2)⟩
  · intro i j h
    rcases h with ⟨x, hx, hy⟩
    cases hi : e i with
    | inl k =>
      simp only [hi, C, Sum.elim_inl] at hy
      change x ∈ closure (p k).realize at hy
      rw [pset, closure_singleton] at hy
      have hxi : x ∈ (C (e i)).realize := by simpa [hi, C, pset] using hy
      have hij : j = i := by
        by_contra hh
        exact Set.disjoint_left.mp (disj (fun he => hh (e.injective he))) hx hxi
      subst j
      exact ⟨subset_closure, Or.inl rfl⟩
    | inr k =>
      simp only [hi, C, Sum.elim_inr] at hy
      change x ∈ closure (g k).realize at hy
      cases hj : e j with
      | inl l =>
        simp only [hj, C, Sum.elim_inl] at hx
        change x ∈ (p l).realize at hx
        have hxx : x = s2v_cad1_coord.symm (d l) := by simpa [pset] using hx
        refine ⟨?_, Or.inr (by simp [D, hi, hj])⟩
        intro y hy'
        have hyy : y = s2v_cad1_coord.symm (d l) := by simpa [hj, C, pset] using hy'
        simpa [hi, C, hyy, hxx] using hy
      | inr l =>
        simp only [hj, C, Sum.elim_inr] at hx
        change x ∈ (g l).realize at hx
        have hlk : l = k := by
          by_contra hh
          rcases lt_or_gt_of_ne hh with hlt | hgt
          · exact gsep l k hlt x hx hy
          · exact gsep' l k hgt x hx hy
        have hij : j = i := e.injective (by rw [hi, hj, hlk])
        subst j
        exact ⟨subset_closure, Or.inl rfl⟩

end HodgeLean.Foundations.Program
