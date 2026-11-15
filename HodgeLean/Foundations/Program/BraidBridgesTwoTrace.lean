import HodgeLean.Foundations.Program.BraidBridgesTwoDefs
import HodgeLean.Foundations.Program.BraidBridges

/-! # Crossing words of the based lasso traces

Each rational piece of a lasso trace contributes its certified crossings, in order for the
forward pieces and reversed with inverted directions for the backward ones. Concatenation along
the reparametrized loop gives the unreduced crossing word.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Crossing data of a real-parametrized downstairs curve on `[s0, s1]`: chronological entries
(cut, direction, time), the exact on-cut set and one-sided signs near each time.
Source: `b65x_CrossesAs`. -/
def b65x_tcSeg (D : ℝ → ℂ) (s0 s1 : ℝ) (L : List (Fin 3 × ℤ × ℝ)) : Prop :=
  L.Pairwise (fun a b ↦ a.2.2 < b.2.2) ∧
  (∀ e ∈ L, s0 < e.2.2 ∧ e.2.2 < s1 ∧ (e.2.1 = 1 ∨ e.2.1 = -1)) ∧
  (∀ (k : Fin 3) (s : ℝ), s0 ≤ s → s ≤ s1 →
    (b65x_OnCut k (D s) ↔ ∃ e ∈ L, e.1 = k ∧ s = e.2.2)) ∧
  ∃ ε : ℝ, 0 < ε ∧ ∀ e ∈ L, ∀ s : ℝ, |s - e.2.2| < ε →
    (s < e.2.2 → (e.2.1 : ℝ) * ((D s).re - b65x_cutPoint e.1) < 0) ∧
    (e.2.2 < s → 0 < (e.2.1 : ℝ) * ((D s).re - b65x_cutPoint e.1))

theorem b65x_tcSeg_append {D : ℝ → ℂ} {s0 s1 s2 : ℝ} {L1 L2 : List (Fin 3 × ℤ × ℝ)}
    (h01 : s0 ≤ s1) (h12 : s1 ≤ s2)
    (h1 : b65x_tcSeg D s0 s1 L1) (h2 : b65x_tcSeg D s1 s2 L2) :
    b65x_tcSeg D s0 s2 (L1 ++ L2) := by
  obtain ⟨p1, b1, c1, ε1, hε1, e1⟩ := h1
  obtain ⟨p2, b2, c2, ε2, hε2, e2⟩ := h2
  refine ⟨List.pairwise_append.mpr ⟨p1, p2, fun a ha b hb ↦ ?_⟩, ?_, ?_, ?_⟩
  · linarith [(b1 a ha).2.1, (b2 b hb).1]
  · intro e he
    rcases List.mem_append.mp he with h | h
    · obtain ⟨x, y, z⟩ := b1 e h
      exact ⟨x, by linarith, z⟩
    · obtain ⟨x, y, z⟩ := b2 e h
      exact ⟨by linarith, y, z⟩
  · intro k s hs0 hs2
    rcases le_total s s1 with h | h
    · rw [c1 k s hs0 h]
      constructor
      · rintro ⟨e, he, rfl, rfl⟩
        exact ⟨e, List.mem_append_left _ he, rfl, rfl⟩
      · rintro ⟨e, he, rfl, rfl⟩
        rcases List.mem_append.mp he with h' | h'
        · exact ⟨e, h', rfl, rfl⟩
        · exact absurd (b2 e h').1 (by linarith)
    · rw [c2 k s h hs2]
      constructor
      · rintro ⟨e, he, rfl, rfl⟩
        exact ⟨e, List.mem_append_right _ he, rfl, rfl⟩
      · rintro ⟨e, he, rfl, rfl⟩
        rcases List.mem_append.mp he with h' | h'
        · exact absurd (b1 e h').2.1 (by linarith)
        · exact ⟨e, h', rfl, rfl⟩
  · refine ⟨min ε1 ε2, lt_min hε1 hε2, fun e he s hs ↦ ?_⟩
    rcases List.mem_append.mp he with h | h
    · exact e1 e h s (lt_of_lt_of_le hs (min_le_left _ _))
    · exact e2 e h s (lt_of_lt_of_le hs (min_le_right _ _))

/-- Crossing data on the whole parameter interval give the chronological crossing word.
Source: `b65x_CrossesAs`. -/
theorem b65x_tcSeg_crossesAs {y : b65x_Down} (d : Path y y) (L : List (Fin 3 × ℤ × ℝ))
    (h : b65x_tcSeg (fun s ↦ (d.extend s).val) 0 1 L) :
    b65x_CrossesAs d (L.map (fun e ↦ (e.1, e.2.1))) := by
  obtain ⟨hp, hb, hc, ε, hε, he⟩ := h
  have hlen : (L.map (fun e ↦ (e.1, e.2.1))).length = L.length := List.length_map _
  let idx : Fin (L.map (fun e ↦ (e.1, e.2.1))).length → Fin L.length := Fin.cast hlen
  have hw : ∀ m : Fin (L.map (fun e ↦ (e.1, e.2.1))).length,
      (L.map (fun e ↦ (e.1, e.2.1)))[m] = ((L[idx m]).1, (L[idx m]).2.1) := by
    intro m
    simp [idx]
  have hmem : ∀ m : Fin L.length, L[m] ∈ L := fun m ↦ List.getElem_mem _
  let u : Fin (L.map (fun e ↦ (e.1, e.2.1))).length → unitInterval := fun m ↦
    ⟨(L[idx m]).2.2, (hb _ (hmem _)).1.le, (hb _ (hmem _)).2.1.le⟩
  have hext : ∀ s : unitInterval, (d.extend s).val = (d s).val := fun s ↦ by
    rw [Path.extend_apply]
  refine ⟨u, ?_, ?_, ?_, ?_, ε, hε, ?_⟩
  · intro m m' hmm
    change (L[idx m]).2.2 < (L[idx m']).2.2
    exact List.pairwise_iff_getElem.mp hp _ _ _ _ (by simpa [idx] using hmm)
  · intro m
    exact ⟨(hb _ (hmem _)).1, (hb _ (hmem _)).2.1⟩
  · intro m
    rw [hw]
    exact (hb _ (hmem _)).2.2
  · intro k s
    have := hc k s s.2.1 s.2.2
    simp only [hext] at this
    rw [this]
    constructor
    · rintro ⟨e, he', rfl, hs⟩
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem he'
      refine ⟨Fin.cast hlen.symm ⟨m, hm⟩, ?_, Subtype.ext ?_⟩
      · rw [hw]; simp [idx]
      · simp [u, idx, hs]
    · rintro ⟨m, hm, rfl⟩
      refine ⟨L[idx m], hmem _, ?_, rfl⟩
      rw [hw] at hm
      exact hm
  · intro m s hs
    rw [hw]
    have := he (L[idx m]) (hmem _) s hs
    simp only [hext] at this
    exact this

theorem b65x_tc_listMin {α : Type*} (L : List α) (g : α → ℝ) (hg : ∀ x ∈ L, 0 < g x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ L, ε ≤ g x := by
  induction L with
  | nil => exact ⟨1, one_pos, fun x hx ↦ absurd hx (by simp)⟩
  | cons a L ih =>
    obtain ⟨ε, hε, h⟩ := ih (fun x hx ↦ hg x (List.mem_cons_of_mem _ hx))
    refine ⟨min ε (g a), lt_min hε (hg a (by simp)), fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h x hx)

/-- Isolating intervals with endpoint signs and a unique root give the exact on-cut set and
one-sided signs of a piece.
Source: B65-BRAIDCERT checker D, cross_piece; intermediate value theorem. -/
theorem b65x_tc_core (f : ℝ → ℂ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (C : List b65x_Crossing)
    (hsort : ∀ m m' : Fin C.length, m < m' → C[m].hi < C[m'].lo)
    (hc : ∀ c ∈ C,
      (c.lo : ℝ) ∈ Set.Icc a b ∧ (c.hi : ℝ) ∈ Set.Icc a b ∧ c.lo < c.hi ∧
      (c.dir = 1 ∨ c.dir = -1) ∧
      (∀ t ∈ Set.Icc (c.lo : ℝ) c.hi, (f t).im < 0) ∧
      (∃! t, t ∈ Set.Icc (c.lo : ℝ) c.hi ∧ (f t).re = b65x_cutPoint c.cut) ∧
      (c.dir : ℝ) * ((f c.lo).re - b65x_cutPoint c.cut) < 0 ∧
      0 < (c.dir : ℝ) * ((f c.hi).re - b65x_cutPoint c.cut))
    (hall : ∀ t ∈ Set.Icc a b, ∀ j : Fin 3, b65x_OnCut j (f t) →
      ∃ c ∈ C, c.cut = j ∧ t ∈ Set.Icc (c.lo : ℝ) c.hi) :
    ∃ τ : b65x_Crossing → ℝ,
      (∀ c ∈ C, (c.lo : ℝ) < τ c ∧ τ c < c.hi ∧
        (∀ t ∈ Set.Icc (c.lo : ℝ) c.hi, t < τ c →
          (c.dir : ℝ) * ((f t).re - b65x_cutPoint c.cut) < 0) ∧
        (∀ t ∈ Set.Icc (c.lo : ℝ) c.hi, τ c < t →
          0 < (c.dir : ℝ) * ((f t).re - b65x_cutPoint c.cut))) ∧
      (∀ t ∈ Set.Icc a b, ∀ j : Fin 3,
        b65x_OnCut j (f t) ↔ ∃ c ∈ C, c.cut = j ∧ t = τ c) ∧
      C.Pairwise (fun c c' ↦ (c.hi : ℝ) < c'.lo) := by
  have hex : ∀ c ∈ C, ∃ t, t ∈ Set.Icc (c.lo : ℝ) c.hi ∧ (f t).re = b65x_cutPoint c.cut :=
    fun c hc' ↦ (hc c hc').2.2.2.2.2.1.exists
  choose! τ hτ using hex
  have hroot : ∀ c ∈ C, ∀ t ∈ Set.Icc (c.lo : ℝ) c.hi,
      (f t).re = b65x_cutPoint c.cut → t = τ c := by
    intro c hc' t ht hre
    exact (hc c hc').2.2.2.2.2.1.unique ⟨ht, hre⟩ (hτ c hc')
  have hzero : ∀ c ∈ C, ∀ t, (c.dir : ℝ) * ((f t).re - b65x_cutPoint c.cut) = 0 →
      (f t).re = b65x_cutPoint c.cut := by
    intro c hc' t h
    have hd : (c.dir : ℝ) ≠ 0 := by
      rcases (hc c hc').2.2.2.1 with h | h <;> simp [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hd)
  have hcont : ∀ c ∈ C, ∀ u v : ℝ, (c.lo : ℝ) ≤ u → v ≤ c.hi →
      ContinuousOn (fun t ↦ (c.dir : ℝ) * ((f t).re - b65x_cutPoint c.cut)) (Set.Icc u v) := by
    intro c hc' u v hu hv
    have hsub : Set.Icc u v ⊆ Set.Icc a b := fun t ht ↦
      ⟨le_trans (hc c hc').1.1 (hu.trans ht.1), le_trans (ht.2.trans hv) (hc c hc').2.1.2⟩
    exact continuousOn_const.mul
      ((Complex.continuous_re.comp_continuousOn (hf.mono hsub)).sub continuousOn_const)
  refine ⟨τ, fun c hc' ↦ ?_, ?_, ?_⟩
  · obtain ⟨hlo, hhi, hlt, -, -, -, hslo, hshi⟩ := hc c hc'
    obtain ⟨⟨hτ1, hτ2⟩, hτre⟩ := hτ c hc'
    have hlt' : (c.lo : ℝ) < c.hi := by exact_mod_cast hlt
    have hne_lo : τ c ≠ c.lo := by
      intro h
      rw [h] at hτre
      rw [hτre, sub_self, mul_zero] at hslo
      exact lt_irrefl _ hslo
    have hne_hi : τ c ≠ c.hi := by
      intro h
      rw [h] at hτre
      rw [hτre, sub_self, mul_zero] at hshi
      exact lt_irrefl _ hshi
    refine ⟨lt_of_le_of_ne hτ1 (Ne.symm hne_lo), lt_of_le_of_ne hτ2 hne_hi, ?_, ?_⟩
    · intro t ht htτ
      by_contra hcon
      rcases (not_lt.mp hcon).lt_or_eq with hpos | h0
      · obtain ⟨t', ht', ht'0⟩ := intermediate_value_Icc ht.1 (hcont c hc' _ _ le_rfl ht.2)
          ⟨hslo.le, hpos.le⟩
        have := hroot c hc' t' ⟨ht'.1, ht'.2.trans ht.2⟩ (hzero c hc' t' ht'0)
        linarith [ht'.2]
      · have := hroot c hc' t ht (hzero c hc' t h0.symm)
        linarith
    · intro t ht hτt
      by_contra hcon
      rcases (not_lt.mp hcon).lt_or_eq with hneg | h0
      · obtain ⟨t', ht', ht'0⟩ := intermediate_value_Icc ht.2 (hcont c hc' _ _ ht.1 le_rfl)
          ⟨hneg.le, hshi.le⟩
        have := hroot c hc' t' ⟨ht.1.trans ht'.1, ht'.2⟩ (hzero c hc' t' ht'0)
        linarith [ht'.1]
      · have := hroot c hc' t ht (hzero c hc' t h0)
        linarith
  · intro t ht j
    constructor
    · intro hj
      obtain ⟨c, hc', hcj, htc⟩ := hall t ht j hj
      refine ⟨c, hc', hcj, hroot c hc' t htc ?_⟩
      rw [hcj]
      exact hj.1
    · rintro ⟨c, hc', rfl, rfl⟩
      exact ⟨(hτ c hc').2, (hc c hc').2.2.2.2.1 _ (hτ c hc').1⟩
  · rw [List.pairwise_iff_getElem]
    intro m m' hm hm' hmm
    exact_mod_cast hsort ⟨m, hm⟩ ⟨m', hm'⟩ hmm

/-- A piece traversed by an increasing reparametrization contributes its crossings in order.
Source: B65-BRAIDCERT checker D, lasso_word; `b65x_tc_core`. -/
theorem b65x_tc_pieceMono (D : ℝ → ℂ) (hD : Continuous D) (f : ℝ → ℂ) (r : ℝ → ℝ)
    (a b s0 s1 : ℝ) (hab : a ≤ b) (hr : StrictMonoOn r (Set.Icc a b))
    (hrc : ContinuousOn r (Set.Icc a b)) (ha : r a = s0) (hb : r b = s1)
    (hDf : ∀ t ∈ Set.Icc a b, D (r t) = f t)
    (C : List b65x_Crossing)
    (hsort : ∀ m m' : Fin C.length, m < m' → C[m].hi < C[m'].lo)
    (hc : ∀ c ∈ C,
      (c.lo : ℝ) ∈ Set.Icc a b ∧ (c.hi : ℝ) ∈ Set.Icc a b ∧ c.lo < c.hi ∧
      (c.dir = 1 ∨ c.dir = -1) ∧
      (∀ t ∈ Set.Icc (c.lo : ℝ) c.hi, (f t).im < 0) ∧
      (∃! t, t ∈ Set.Icc (c.lo : ℝ) c.hi ∧ (f t).re = b65x_cutPoint c.cut) ∧
      (c.dir : ℝ) * ((f c.lo).re - b65x_cutPoint c.cut) < 0 ∧
      0 < (c.dir : ℝ) * ((f c.hi).re - b65x_cutPoint c.cut))
    (hall : ∀ t ∈ Set.Icc a b, ∀ j : Fin 3, b65x_OnCut j (f t) →
      ∃ c ∈ C, c.cut = j ∧ t ∈ Set.Icc (c.lo : ℝ) c.hi) :
    ∃ τ : b65x_Crossing → ℝ, b65x_tcSeg D s0 s1 (C.map fun c ↦ (c.cut, c.dir, r (τ c))) := by
  have hf : ContinuousOn f (Set.Icc a b) :=
    (hD.comp_continuousOn hrc).congr (fun t ht ↦ (hDf t ht).symm)
  obtain ⟨τ, h1, h2, h3⟩ := b65x_tc_core f a b hf C hsort hc hall
  have hsurj : ∀ s ∈ Set.Icc s0 s1, ∃ t ∈ Set.Icc a b, r t = s := by
    intro s hs
    rw [← ha, ← hb] at hs
    exact intermediate_value_Icc hab hrc hs
  have hτab : ∀ c ∈ C, τ c ∈ Set.Icc a b := fun c hc' ↦
    ⟨(hc c hc').1.1.trans (h1 c hc').1.le, (h1 c hc').2.1.le.trans (hc c hc').2.1.2⟩
  have hloab : ∀ c ∈ C, (c.lo : ℝ) ∈ Set.Icc a b := fun c hc' ↦ (hc c hc').1
  have hhiab : ∀ c ∈ C, (c.hi : ℝ) ∈ Set.Icc a b := fun c hc' ↦ (hc c hc').2.1
  have haab : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbab : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact h3.imp_of_mem (fun {c c'} hc' hc'' h ↦ hr (hτab c hc') (hτab c' hc'')
      (by linarith [(h1 c hc').2.1, (h1 c' hc'').1]))
  · intro e he
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp he
    refine ⟨?_, ?_, (hc c hc').2.2.2.1⟩
    · rw [← ha]
      exact hr haab (hτab c hc') (by linarith [(hc c hc').1.1, (h1 c hc').1])
    · rw [← hb]
      exact hr (hτab c hc') hbab (by linarith [(hc c hc').2.1.2, (h1 c hc').2.1])
  · intro k s hs0 hs1
    obtain ⟨t, ht, rfl⟩ := hsurj s ⟨hs0, hs1⟩
    rw [hDf t ht, h2 t ht k]
    constructor
    · rintro ⟨c, hc', rfl, rfl⟩
      exact ⟨_, List.mem_map_of_mem hc', rfl, rfl⟩
    · rintro ⟨e, he, hk, hs⟩
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp he
      exact ⟨c, hc', hk, hr.injOn ht (hτab c hc') hs⟩
  · obtain ⟨ε, hε, hmin⟩ := b65x_tc_listMin C
      (fun c ↦ min (r (τ c) - r c.lo) (r c.hi - r (τ c)))
      (fun c hc' ↦ lt_min (sub_pos.mpr (hr (hloab c hc') (hτab c hc') (h1 c hc').1))
        (sub_pos.mpr (hr (hτab c hc') (hhiab c hc') (h1 c hc').2.1)))
    refine ⟨ε, hε, ?_⟩
    intro e he s hs
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp he
    have hm := hmin c hc'
    have hs' := abs_lt.mp hs
    have hm1 := min_le_left (r (τ c) - r c.lo) (r c.hi - r (τ c))
    have hm2 := min_le_right (r (τ c) - r c.lo) (r c.hi - r (τ c))
    simp only at hs' hm hm1 hm2 ⊢
    have hslo : r c.lo < s := by linarith
    have hshi : s < r c.hi := by linarith
    have hs01 : s ∈ Set.Icc s0 s1 := by
      rw [← ha, ← hb]
      exact ⟨(hr.monotoneOn haab (hloab c hc') (hloab c hc').1).trans hslo.le,
        hshi.le.trans (hr.monotoneOn (hhiab c hc') hbab (hhiab c hc').2)⟩
    obtain ⟨t, ht, rfl⟩ := hsurj s hs01
    have htlo : (c.lo : ℝ) < t := (hr.lt_iff_lt (hloab c hc') ht).mp hslo
    have hthi : t < c.hi := (hr.lt_iff_lt ht (hhiab c hc')).mp hshi
    rw [hDf t ht]
    constructor
    · intro hlt
      exact (h1 c hc').2.2.1 t ⟨htlo.le, hthi.le⟩ ((hr.lt_iff_lt ht (hτab c hc')).mp hlt)
    · intro hlt
      exact (h1 c hc').2.2.2 t ⟨htlo.le, hthi.le⟩ ((hr.lt_iff_lt (hτab c hc') ht).mp hlt)

/-- A piece traversed by a decreasing reparametrization contributes its crossings backwards,
with inverted directions.
Source: B65-BRAIDCERT checker D, word_piece with rev; `b65x_tc_core`. -/
theorem b65x_tc_pieceAnti (D : ℝ → ℂ) (hD : Continuous D) (f : ℝ → ℂ) (r : ℝ → ℝ)
    (a b s0 s1 : ℝ) (hab : a ≤ b) (hr : StrictAntiOn r (Set.Icc a b))
    (hrc : ContinuousOn r (Set.Icc a b)) (ha : r a = s1) (hb : r b = s0)
    (hDf : ∀ t ∈ Set.Icc a b, D (r t) = f t)
    (C : List b65x_Crossing)
    (hsort : ∀ m m' : Fin C.length, m < m' → C[m].hi < C[m'].lo)
    (hc : ∀ c ∈ C,
      (c.lo : ℝ) ∈ Set.Icc a b ∧ (c.hi : ℝ) ∈ Set.Icc a b ∧ c.lo < c.hi ∧
      (c.dir = 1 ∨ c.dir = -1) ∧
      (∀ t ∈ Set.Icc (c.lo : ℝ) c.hi, (f t).im < 0) ∧
      (∃! t, t ∈ Set.Icc (c.lo : ℝ) c.hi ∧ (f t).re = b65x_cutPoint c.cut) ∧
      (c.dir : ℝ) * ((f c.lo).re - b65x_cutPoint c.cut) < 0 ∧
      0 < (c.dir : ℝ) * ((f c.hi).re - b65x_cutPoint c.cut))
    (hall : ∀ t ∈ Set.Icc a b, ∀ j : Fin 3, b65x_OnCut j (f t) →
      ∃ c ∈ C, c.cut = j ∧ t ∈ Set.Icc (c.lo : ℝ) c.hi) :
    ∃ τ : b65x_Crossing → ℝ,
      b65x_tcSeg D s0 s1 (C.map fun c ↦ (c.cut, -c.dir, r (τ c))).reverse := by
  have hf : ContinuousOn f (Set.Icc a b) :=
    (hD.comp_continuousOn hrc).congr (fun t ht ↦ (hDf t ht).symm)
  obtain ⟨τ, h1, h2, h3⟩ := b65x_tc_core f a b hf C hsort hc hall
  have hsurj : ∀ s ∈ Set.Icc s0 s1, ∃ t ∈ Set.Icc a b, r t = s := by
    intro s hs
    rw [← ha, ← hb] at hs
    exact intermediate_value_Icc' hab hrc hs
  have hτab : ∀ c ∈ C, τ c ∈ Set.Icc a b := fun c hc' ↦
    ⟨(hc c hc').1.1.trans (h1 c hc').1.le, (h1 c hc').2.1.le.trans (hc c hc').2.1.2⟩
  have hloab : ∀ c ∈ C, (c.lo : ℝ) ∈ Set.Icc a b := fun c hc' ↦ (hc c hc').1
  have hhiab : ∀ c ∈ C, (c.hi : ℝ) ∈ Set.Icc a b := fun c hc' ↦ (hc c hc').2.1
  have haab : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbab : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_reverse, List.pairwise_map]
    exact h3.imp_of_mem (fun {c c'} hc' hc'' h ↦ hr (hτab c hc') (hτab c' hc'')
      (by linarith [(h1 c hc').2.1, (h1 c' hc'').1]))
  · intro e he
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    refine ⟨?_, ?_, ?_⟩
    · rw [← hb]
      exact hr (hτab c hc') hbab (by linarith [(hc c hc').2.1.2, (h1 c hc').2.1])
    · rw [← ha]
      exact hr haab (hτab c hc') (by linarith [(hc c hc').1.1, (h1 c hc').1])
    · rcases (hc c hc').2.2.2.1 with h | h <;> simp [h]
  · intro k s hs0 hs1
    obtain ⟨t, ht, rfl⟩ := hsurj s ⟨hs0, hs1⟩
    rw [hDf t ht, h2 t ht k]
    constructor
    · rintro ⟨c, hc', rfl, rfl⟩
      exact ⟨_, List.mem_reverse.mpr (List.mem_map_of_mem hc'), rfl, rfl⟩
    · rintro ⟨e, he, hk, hs⟩
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      exact ⟨c, hc', hk, hr.injOn ht (hτab c hc') hs⟩
  · obtain ⟨ε, hε, hmin⟩ := b65x_tc_listMin C
      (fun c ↦ min (r c.lo - r (τ c)) (r (τ c) - r c.hi))
      (fun c hc' ↦ lt_min (sub_pos.mpr (hr (hloab c hc') (hτab c hc') (h1 c hc').1))
        (sub_pos.mpr (hr (hτab c hc') (hhiab c hc') (h1 c hc').2.1)))
    refine ⟨ε, hε, ?_⟩
    intro e he s hs
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    have hm := hmin c hc'
    have hs' := abs_lt.mp hs
    have hm1 := min_le_left (r c.lo - r (τ c)) (r (τ c) - r c.hi)
    have hm2 := min_le_right (r c.lo - r (τ c)) (r (τ c) - r c.hi)
    simp only at hs' hm hm1 hm2 ⊢
    have hslo : s < r c.lo := by linarith
    have hshi : r c.hi < s := by linarith
    have hs01 : s ∈ Set.Icc s0 s1 := by
      rw [← ha, ← hb]
      exact ⟨(hr.antitoneOn (hhiab c hc') hbab (hhiab c hc').2).trans hshi.le,
        hslo.le.trans (hr.antitoneOn haab (hloab c hc') (hloab c hc').1)⟩
    obtain ⟨t, ht, rfl⟩ := hsurj s hs01
    have htlo : (c.lo : ℝ) < t := (hr.lt_iff_gt ht (hloab c hc')).mp hslo
    have hthi : t < c.hi := (hr.lt_iff_gt (hhiab c hc') ht).mp hshi
    rw [hDf t ht]
    push_cast
    constructor
    · intro hlt
      have := (h1 c hc').2.2.2 t ⟨htlo.le, hthi.le⟩ ((hr.lt_iff_gt ht (hτab c hc')).mp hlt)
      linarith
    · intro hlt
      have := (h1 c hc').2.2.1 t ⟨htlo.le, hthi.le⟩ ((hr.lt_iff_gt (hτab c hc') ht).mp hlt)
      linarith

theorem b65x_tc_arctan_mono (c0 : ℝ) :
    StrictMono (fun t : ℝ ↦ (c0 + Real.arctan t / Real.pi) / 3) := by
  intro x y h
  have h1 := Real.arctan_strictMono h
  have h2 : Real.arctan x / Real.pi < Real.arctan y / Real.pi := div_lt_div_of_pos_right h1 Real.pi_pos
  simp only
  linarith

theorem b65x_tc_arctan_anti (c0 : ℝ) :
    StrictAnti (fun t : ℝ ↦ c0 - Real.arctan t / Real.pi) := by
  intro x y h
  have h1 := Real.arctan_strictMono h
  have h2 : Real.arctan x / Real.pi < Real.arctan y / Real.pi := div_lt_div_of_pos_right h1 Real.pi_pos
  simp only
  linarith

theorem b65x_tc_arctan_div_one : Real.arctan 1 / Real.pi = 1 / 4 := by
  rw [Real.arctan_one]
  field_simp

theorem b65x_tc_arctan_div_neg_one : Real.arctan (-1) / Real.pi = -(1 / 4) := by
  rw [Real.arctan_neg, neg_div, b65x_tc_arctan_div_one]

theorem b65x_tc_arctan_cont (c0 : ℝ) :
    Continuous (fun t : ℝ ↦ (c0 + Real.arctan t / Real.pi) / 3) := by
  fun_prop

theorem b65x_tc_arctan_cont' (c0 : ℝ) :
    Continuous (fun t : ℝ ↦ c0 - Real.arctan t / Real.pi) := by
  fun_prop

theorem b65x_tc_range_mono (c0 : ℝ) (hlo : 0 ≤ (c0 - 1/4) / 3) (hhi : (c0 + 1/4) / 3 ≤ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (c0 + Real.arctan t / Real.pi) / 3 ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := (b65x_tc_arctan_mono c0).monotone ht.1
  have h2 := (b65x_tc_arctan_mono c0).monotone ht.2
  simp only [b65x_tc_arctan_div_one, b65x_tc_arctan_div_neg_one] at h1 h2
  constructor <;> linarith

theorem b65x_tc_range_anti (c0 : ℝ) (hlo : 0 ≤ c0 - 1/4) (hhi : c0 + 1/4 ≤ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    c0 - Real.arctan t / Real.pi ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := (b65x_tc_arctan_anti c0).antitone ht.1
  have h2 := (b65x_tc_arctan_anti c0).antitone ht.2
  simp only [b65x_tc_arctan_div_one, b65x_tc_arctan_div_neg_one] at h1 h2
  constructor <;> linarith

theorem b65x_tc_outer (D : ℝ → ℂ) (hDc : Continuous D)
    (hDpiece : ∀ (k : Fin 3) (s t : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      b65b_lasso 0 s = b65x_piece 0 k t → D s = b65x_down 0 k t) :
    ∃ L, b65x_tcSeg D 0 1 L ∧ L.map (fun e ↦ (e.1, e.2.1)) = b65x_rawWord 0 := by
  obtain ⟨-, -, hL3⟩ := b65x_lasso_pieces
  have hdom1 : b65x_dom 1 = Set.Icc (-1) 1 := by simp [b65x_dom]
  have hdom2 : b65x_dom 2 = Set.Icc (-1) 1 := by simp [b65x_dom]
  obtain ⟨hs1, hc1, ha1⟩ := b65x_piece_crossings 0 1
  obtain ⟨hs2, hc2, ha2⟩ := b65x_piece_crossings 0 2
  rw [hdom1] at hc1 ha1
  rw [hdom2] at hc2 ha2
  have hn1 := b65x_tc_arctan_div_one
  have hn2 := b65x_tc_arctan_div_neg_one
  obtain ⟨τ2, hseg2⟩ := b65x_tc_pieceAnti D hDc (b65x_down 0 2)
    (fun t ↦ 1/4 - Real.arctan t / Real.pi) (-1) 1 0 (1/2) (by norm_num)
    ((b65x_tc_arctan_anti _).strictAntiOn _) (b65x_tc_arctan_cont' _).continuousOn
    (by show 1/4 - Real.arctan (-1) / Real.pi = 1/2; rw [hn2]; norm_num)
    (by show 1/4 - Real.arctan 1 / Real.pi = 0; rw [hn1]; norm_num)
    (fun t ht ↦ hDpiece 2 _ t (b65x_tc_range_anti _ (by norm_num) (by norm_num) t ht)
      (hL3 t ht).1) _ hs2 hc2 ha2
  obtain ⟨τ1, hseg1⟩ := b65x_tc_pieceAnti D hDc (b65x_down 0 1)
    (fun t ↦ 3/4 - Real.arctan t / Real.pi) (-1) 1 (1/2) 1 (by norm_num)
    ((b65x_tc_arctan_anti _).strictAntiOn _) (b65x_tc_arctan_cont' _).continuousOn
    (by show 3/4 - Real.arctan (-1) / Real.pi = 1; rw [hn2]; norm_num)
    (by show 3/4 - Real.arctan 1 / Real.pi = 1/2; rw [hn1]; norm_num)
    (fun t ht ↦ hDpiece 1 _ t (b65x_tc_range_anti _ (by norm_num) (by norm_num) t ht)
      (hL3 t ht).2) _ hs1 hc1 ha1
  refine ⟨_, b65x_tcSeg_append (by norm_num) (by norm_num) hseg2 hseg1, ?_⟩
  simp [b65x_rawWord, b65x_back, b65x_letters, List.map_reverse, Function.comp_def]

theorem b65x_tc_inner (i : Fin 13) (hi : i ≠ 0) (D : ℝ → ℂ) (hDc : Continuous D)
    (hDpiece : ∀ (k : Fin 3) (s t : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      b65b_lasso i s = b65x_piece i k t → D s = b65x_down i k t) :
    ∃ L, b65x_tcSeg D 0 1 L ∧ L.map (fun e ↦ (e.1, e.2.1)) = b65x_rawWord i := by
  obtain ⟨hL1, hL2, -⟩ := b65x_lasso_pieces
  have hdom0 : b65x_dom 0 = Set.Icc 0 1 := by simp [b65x_dom]
  have hdom1 : b65x_dom 1 = Set.Icc (-1) 1 := by simp [b65x_dom]
  have hdom2 : b65x_dom 2 = Set.Icc (-1) 1 := by simp [b65x_dom]
  obtain ⟨hs0, hc0, ha0⟩ := b65x_piece_crossings i 0
  obtain ⟨hs1, hc1, ha1⟩ := b65x_piece_crossings i 1
  obtain ⟨hs2, hc2, ha2⟩ := b65x_piece_crossings i 2
  rw [hdom0] at hc0 ha0
  rw [hdom1] at hc1 ha1
  rw [hdom2] at hc2 ha2
  have hn1 := b65x_tc_arctan_div_one
  have hn2 := b65x_tc_arctan_div_neg_one
  have hm3 : StrictAnti (fun t : ℝ ↦ 1 - t / 3) := by
    intro a b h; simp only; linarith
  have hm0 : StrictMono (fun t : ℝ ↦ t / 3) := by
    intro a b h; simp only; linarith
  obtain ⟨τ0, hseg0⟩ := b65x_tc_pieceMono D hDc (b65x_down i 0) (fun t ↦ t / 3) 0 1 0 (1/3)
    (by norm_num) (hm0.strictMonoOn _) (by fun_prop) (by norm_num) (by norm_num)
    (fun t ht ↦ hDpiece 0 _ t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (hL1 i hi t ht).1)
    _ hs0 hc0 ha0
  obtain ⟨τ1, hseg1⟩ := b65x_tc_pieceMono D hDc (b65x_down i 1)
    (fun t ↦ (5/4 + Real.arctan t / Real.pi) / 3) (-1) 1 (1/3) (1/2) (by norm_num)
    ((b65x_tc_arctan_mono _).strictMonoOn _) (b65x_tc_arctan_cont _).continuousOn
    (by show (5/4 + Real.arctan (-1) / Real.pi) / 3 = 1/3; rw [hn2]; norm_num)
    (by show (5/4 + Real.arctan 1 / Real.pi) / 3 = 1/2; rw [hn1]; norm_num)
    (fun t ht ↦ hDpiece 1 _ t (b65x_tc_range_mono _ (by norm_num) (by norm_num) t ht)
      (hL2 i hi t ht).1) _ hs1 hc1 ha1
  obtain ⟨τ2, hseg2⟩ := b65x_tc_pieceMono D hDc (b65x_down i 2)
    (fun t ↦ (7/4 + Real.arctan t / Real.pi) / 3) (-1) 1 (1/2) (2/3) (by norm_num)
    ((b65x_tc_arctan_mono _).strictMonoOn _) (b65x_tc_arctan_cont _).continuousOn
    (by show (7/4 + Real.arctan (-1) / Real.pi) / 3 = 1/2; rw [hn2]; norm_num)
    (by show (7/4 + Real.arctan 1 / Real.pi) / 3 = 2/3; rw [hn1]; norm_num)
    (fun t ht ↦ hDpiece 2 _ t (b65x_tc_range_mono _ (by norm_num) (by norm_num) t ht)
      (hL2 i hi t ht).2) _ hs2 hc2 ha2
  obtain ⟨τ3, hseg3⟩ := b65x_tc_pieceAnti D hDc (b65x_down i 0) (fun t ↦ 1 - t / 3) 0 1
    (2/3) 1 (by norm_num) (hm3.strictAntiOn _) (by fun_prop) (by norm_num) (by norm_num)
    (fun t ht ↦ hDpiece 0 _ t ⟨by linarith [ht.2], by linarith [ht.1]⟩ (hL1 i hi t ht).2)
    _ hs0 hc0 ha0
  refine ⟨_, b65x_tcSeg_append (by norm_num) (by norm_num)
    (b65x_tcSeg_append (by norm_num) (by norm_num)
      (b65x_tcSeg_append (by norm_num) (by norm_num) hseg0 hseg1) hseg2) hseg3, ?_⟩
  simp [b65x_rawWord, hi, b65x_back, b65x_letters, List.map_reverse, Function.comp_def]

/-- Assembly of the certified piece words along the based lasso trace.
Source: B65-BRAIDCERT checker D, lasso_word and OW; `b65x_lasso_pieces` and
`b65x_piece_crossings`. -/
theorem b65x_tc_trace (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso i s)) (i : Fin 13) :
    b65x_CrossesAs ((δ i).map b65x_phiMap.continuous) (b65x_rawWord i) := by
  let d := (δ i).map b65x_phiMap.continuous
  let D : ℝ → ℂ := fun s ↦ (d.extend s).val
  have hDc : Continuous D := continuous_subtype_val.comp d.continuous_extend
  have hDpiece : ∀ (k : Fin 3) (s t : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      b65b_lasso i s = b65x_piece i k t → D s = b65x_down i k t := by
    intro k s t hs heq
    change ((d.extend s) : ℂ) = _
    rw [Path.extend_apply _ hs]
    change b65r_phi ((δ i ⟨s, hs⟩).val) = _
    rw [hδ, show ((⟨s, hs⟩ : unitInterval) : ℝ) = s from rfl, heq]
    rfl
  obtain ⟨L, hL, hw⟩ : ∃ L, b65x_tcSeg D 0 1 L ∧
      L.map (fun e ↦ (e.1, e.2.1)) = b65x_rawWord i := by
    by_cases hi : i = 0
    · subst hi
      exact b65x_tc_outer D hDc hDpiece
    · exact b65x_tc_inner i hi D hDc hDpiece
  rw [← hw]
  exact b65x_tcSeg_crossesAs d L hL

end HodgeLean.Foundations.Program
