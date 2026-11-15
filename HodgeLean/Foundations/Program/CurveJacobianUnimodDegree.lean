import Mathlib

/-! # Track B3, lane Unimod: the degree of a real function with periodic increments

Let `g : ℝ → ℝ` be `C¹` with `g (t + 1) = g t + n` and `0` a regular value of `g` mod `1`: at every
`t` with `g t ∈ ℤ`, `g' t ≠ 0`. Then the integer crossings `t ∈ [0, 1)`, counted with the sign of
`g' t`, add up to `n` (`b3Unimod_degree`). The right-continuous floor
`R t = ⌊g t⌋ - [g t ∈ ℤ ∧ g' t < 0]` jumps by `sign g' t` exactly at the crossings, so
`R - J` is locally constant on `[0, 1]`, with `J t` the signed count of crossings in `(0, t]`.

`b3Unimod_exists_regular`: for finitely many `C¹` functions `F j` there is a level `c` outside a
given countable set with `F j t ∈ c + ℤ ⇒ F' j t ≠ 0` on `[0, 1]` (the critical values have
measure zero).
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace HodgeLean.Foundations.Program

section Degree

variable {g g' : ℝ → ℝ}

open scoped Classical in
/-- The right-continuous floor of `g`. -/
def b3Unimod_R (g g' : ℝ → ℝ) (t : ℝ) : ℤ :=
  if (∃ m : ℤ, g t = m) ∧ g' t < 0 then ⌊g t⌋ - 1 else ⌊g t⌋

/-- The signed count of the crossings of a finite set `S` up to `t`. -/
def b3Unimod_J (g' : ℝ → ℝ) (S : Finset ℝ) (t : ℝ) : ℤ :=
  ∑ s ∈ S.filter (· ≤ t), ((SignType.sign (g' s) : SignType) : ℤ)

theorem b3Unimod_R_of_not_int {t : ℝ} (h : ¬ ∃ m : ℤ, g t = m) : b3Unimod_R g g' t = ⌊g t⌋ := by
  unfold b3Unimod_R
  exact ite_eq_right fun h' : (∃ m : ℤ, g t = m) ∧ g' t < 0 ↦ h h'.1

theorem b3Unimod_R_of_neg {t : ℝ} {m : ℤ} (hm : g t = m) (h : g' t < 0) :
    b3Unimod_R g g' t = m - 1 := by
  unfold b3Unimod_R
  rw [ite_eq_left ⟨⟨m, hm⟩, h⟩, hm, Int.floor_intCast]

theorem b3Unimod_R_of_pos {t : ℝ} {m : ℤ} (hm : g t = m) (h : 0 < g' t) :
    b3Unimod_R g g' t = m := by
  unfold b3Unimod_R
  rw [ite_eq_right fun h' : (∃ m : ℤ, g t = m) ∧ g' t < 0 ↦ (not_lt.2 h.le) h'.2, hm,
    Int.floor_intCast]

theorem b3Unimod_J_eq_of_no_between (g' : ℝ → ℝ) (S : Finset ℝ) {x t : ℝ}
    (h : ∀ s ∈ S, ¬ (min x t < s ∧ s ≤ max x t)) : b3Unimod_J g' S x = b3Unimod_J g' S t := by
  unfold b3Unimod_J
  congr 1
  ext s
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hs
  have := h s hs
  constructor
  · intro hsx
    by_contra hst
    push Not at hst
    exact this ⟨lt_of_lt_of_le' hst (min_le_right _ _), hsx.trans (le_max_left _ _)⟩
  · intro hst
    by_contra hsx
    push Not at hsx
    exact this ⟨lt_of_lt_of_le' hsx (min_le_left _ _), hst.trans (le_max_right _ _)⟩

theorem b3Unimod_J_left (g' : ℝ → ℝ) (S : Finset ℝ) {x t : ℝ} (hxt : x < t)
    (h : ∀ s ∈ S, x < s → s < t → False) :
    b3Unimod_J g' S t = b3Unimod_J g' S x +
      if t ∈ S then ((SignType.sign (g' t) : SignType) : ℤ) else 0 := by
  classical
  unfold b3Unimod_J
  have hset : S.filter (· ≤ t) = S.filter (· ≤ x) ∪ (S.filter (· = t)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hs, hst⟩
      rcases hst.lt_or_eq with hst | hst
      · left
        refine ⟨hs, ?_⟩
        by_contra hsx
        exact h s hs (lt_of_not_ge hsx) hst
      · exact Or.inr ⟨hs, hst⟩
    · rintro (⟨hs, hsx⟩ | ⟨hs, rfl⟩)
      · exact ⟨hs, hsx.trans hxt.le⟩
      · exact ⟨hs, le_rfl⟩
  have hdisj : Disjoint (S.filter (· ≤ x)) (S.filter (· = t)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_filter] at hs1 hs2
    rw [hs2.2] at hs1
    linarith [hs1.2]
  rw [hset, Finset.sum_union hdisj]
  congr 1
  split_ifs with ht
  · rw [show S.filter (· = t) = {t} by
      ext s
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ ht, h⟩⟩]
    simp
  · rw [show S.filter (· = t) = ∅ by
      ext s
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      rintro hs rfl
      exact ht hs]
    simp

theorem b3Unimod_floor_of_mem {y : ℝ} {m : ℤ} (h1 : (m : ℝ) - 1 < y) (h2 : y < m) :
    ⌊y⌋ = m - 1 ∧ ¬ ∃ k : ℤ, y = k := by
  refine ⟨Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩, ?_⟩
  rintro ⟨k, rfl⟩
  have a : m - 1 < k := by exact_mod_cast h1
  have b : k < m := by exact_mod_cast h2
  omega

theorem b3Unimod_floor_of_mem' {y : ℝ} {m : ℤ} (h1 : (m : ℝ) < y) (h2 : y < m + 1) :
    ⌊y⌋ = m ∧ ¬ ∃ k : ℤ, y = k := by
  have := b3Unimod_floor_of_mem (y := y) (m := m + 1) (by push_cast; linarith)
    (by push_cast; linarith)
  simpa using this

variable (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
include hg hg'

/-- Near a regular integer crossing, `g` is strictly monotone and within distance `1` of it. -/
theorem b3Unimod_local_mono {t : ℝ} (hne : g' t ≠ 0) :
    ∃ ε > 0, (∀ x ∈ Metric.ball t ε, |g x - g t| < 1) ∧
      (0 < g' t → StrictMonoOn g (Metric.ball t ε)) ∧
      (g' t < 0 → StrictAntiOn g (Metric.ball t ε)) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t ↦ (hg t).continuousAt
  have h1 : ∀ᶠ x in 𝓝 t, |g x - g t| < 1 := by
    have := (hgc.tendsto t).eventually (Metric.ball_mem_nhds (g t) one_pos)
    filter_upwards [this] with x hx
    rwa [Real.dist_eq] at hx
  have h2 : ∀ᶠ x in 𝓝 t, SignType.sign (g' x) = SignType.sign (g' t) := by
    rcases hne.lt_or_gt with h | h
    · filter_upwards [(hg'.tendsto t).eventually (gt_mem_nhds h)] with x hx
      rw [sign_neg hx, sign_neg h]
    · filter_upwards [(hg'.tendsto t).eventually (lt_mem_nhds h)] with x hx
      rw [sign_pos hx, sign_pos h]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (h1.and h2)
  refine ⟨ε, hε, fun x hx ↦ (hball hx).1, fun hpos ↦ ?_, fun hneg ↦ ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_ball t ε)
      (fun x _ ↦ (hg x).continuousAt.continuousWithinAt) fun x hx ↦ ?_
    rw [interior_eq_iff_isOpen.2 Metric.isOpen_ball] at hx
    rw [(hg x).deriv]
    have := (hball hx).2
    rw [sign_pos hpos, sign_eq_one_iff] at this
    exact this
  · refine strictAntiOn_of_deriv_neg (convex_ball t ε)
      (fun x _ ↦ (hg x).continuousAt.continuousWithinAt) fun x hx ↦ ?_
    rw [interior_eq_iff_isOpen.2 Metric.isOpen_ball] at hx
    rw [(hg x).deriv]
    have := (hball hx).2
    rw [sign_neg hneg, sign_eq_neg_one_iff] at this
    exact this

/-- **`R - J` is locally constant on `[0, 1]`.** -/
theorem b3Unimod_locallyConst (S : Finset ℝ)
    (hS : ∀ s, s ∈ S ↔ s ∈ Ioc (0 : ℝ) 1 ∧ ∃ m : ℤ, g s = m)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (∃ m : ℤ, g t = m) → g' t ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ x in 𝓝 t, x ∈ Icc (0 : ℝ) 1 →
      b3Unimod_R g g' x - b3Unimod_J g' S x = b3Unimod_R g g' t - b3Unimod_J g' S t := by
  classical
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t ↦ (hg t).continuousAt
  -- no other point of `S` near `t`
  have hsep : ∀ᶠ x in 𝓝 t, x ∉ (S.erase t : Set ℝ) :=
    (S.erase t).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.mem_nhds_iff.1 hsep
  have hnoS : ∀ x ∈ Metric.ball t ε₀, ∀ s ∈ S, min x t < s → s ≤ max x t → s = t := by
    intro x hx s hs h1 h2
    by_contra hst
    refine hball₀ ?_ (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hst, hs⟩))
    rw [Metric.mem_ball, Real.dist_eq] at hx ⊢
    rw [abs_lt] at hx ⊢
    constructor
    · rcases le_total x t with h | h
      · rw [min_eq_left h] at h1; linarith
      · rw [min_eq_right h] at h1; linarith
    · rcases le_total x t with h | h
      · rw [max_eq_right h] at h2; linarith
      · rw [max_eq_left h] at h2; linarith
  by_cases hint : ∃ m : ℤ, g t = m
  · obtain ⟨m, hm⟩ := hint
    have hne := hreg t ht ⟨m, hm⟩
    obtain ⟨ε, hε, hnear, hmono, hanti⟩ := b3Unimod_local_mono hg hg' hne
    filter_upwards [Metric.ball_mem_nhds t (lt_min hε hε₀)] with x hx hxI
    have hxε : x ∈ Metric.ball t ε := Metric.ball_subset_ball (min_le_left _ _) hx
    have hxε₀ : x ∈ Metric.ball t ε₀ := Metric.ball_subset_ball (min_le_right _ _) hx
    have hd := hnear x hxε
    rw [hm, abs_lt] at hd
    have htI : t ∈ Metric.ball t ε := Metric.mem_ball_self hε
    rcases lt_trichotomy x t with hxt | rfl | hxt
    · -- left of the crossing: `t` is the only point of `S` in `(x, t]`
      have hJ := b3Unimod_J_left g' S hxt fun s hs h1 h2 ↦ by
        have := hnoS x hxε₀ s hs (by rwa [min_eq_left hxt.le]) (by
          rw [max_eq_right hxt.le]; exact h2.le)
        linarith
      have htS : t ≠ 0 → t ∈ S := fun h0 ↦ (hS t).2 ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩,
        ⟨m, hm⟩⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact absurd hxI.1 (not_le.2 hxt)
      rw [ite_eq_left (htS ht0)] at hJ
      rcases hne.lt_or_gt with hneg | hpos
      · have hlt := hanti hneg hxε htI hxt
        rw [hm] at hlt
        obtain ⟨hf, hni⟩ := b3Unimod_floor_of_mem' (y := g x) (m := m) hlt (by linarith)
        have hRx : b3Unimod_R g g' x = m := by
          rw [b3Unimod_R_of_not_int hni, hf]
        have hRt : b3Unimod_R g g' t = m - 1 := b3Unimod_R_of_neg hm hneg
        rw [hRx, hRt, hJ, sign_neg hneg]
        simp
        ring
      · have hlt := hmono hpos hxε htI hxt
        rw [hm] at hlt
        obtain ⟨hf, hni⟩ := b3Unimod_floor_of_mem (y := g x) (m := m) (by linarith) hlt
        have hRx : b3Unimod_R g g' x = m - 1 := by
          rw [b3Unimod_R_of_not_int hni, hf]
        have hRt : b3Unimod_R g g' t = m := b3Unimod_R_of_pos hm hpos
        rw [hRx, hRt, hJ, sign_pos hpos]
        simp only [SignType.coe_one]
        ring
    · rfl
    · -- right of the crossing: no point of `S` in `(t, x]`
      have hJ := b3Unimod_J_eq_of_no_between g' S (x := x) (t := t) fun s hs ⟨h1, h2⟩ ↦ by
        have := hnoS x hxε₀ s hs h1 h2
        rw [min_eq_right hxt.le] at h1
        linarith
      rcases hne.lt_or_gt with hneg | hpos
      · have hlt := hanti hneg htI hxε hxt
        rw [hm] at hlt
        obtain ⟨hf, hni⟩ := b3Unimod_floor_of_mem (y := g x) (m := m) (by linarith) hlt
        have hRx : b3Unimod_R g g' x = m - 1 := by
          rw [b3Unimod_R_of_not_int hni, hf]
        have hRt : b3Unimod_R g g' t = m - 1 := b3Unimod_R_of_neg hm hneg
        rw [hRx, hRt, hJ]
      · have hlt := hmono hpos htI hxε hxt
        rw [hm] at hlt
        obtain ⟨hf, hni⟩ := b3Unimod_floor_of_mem' (y := g x) (m := m) hlt (by linarith)
        have hRx : b3Unimod_R g g' x = m := by
          rw [b3Unimod_R_of_not_int hni, hf]
        have hRt : b3Unimod_R g g' t = m := b3Unimod_R_of_pos hm hpos
        rw [hRx, hRt, hJ]
  · -- `g t` is not an integer: the floor and the count are locally constant
    push Not at hint
    set m := ⌊g t⌋
    have h1 : (m : ℝ) < g t := lt_of_le_of_ne (Int.floor_le _) (fun h ↦ hint m h.symm)
    have h2 : g t < m + 1 := Int.lt_floor_add_one _
    have hev : ∀ᶠ x in 𝓝 t, (m : ℝ) < g x ∧ g x < m + 1 :=
      ((hgc.tendsto t).eventually (lt_mem_nhds h1)).and
        ((hgc.tendsto t).eventually (gt_mem_nhds h2))
    have htS : t ∉ S := fun h ↦ hint _ ((hS t).1 h).2.choose_spec
    filter_upwards [hev, Metric.ball_mem_nhds t hε₀] with x hx hxb _
    obtain ⟨hf, hni⟩ := b3Unimod_floor_of_mem' hx.1 hx.2
    obtain ⟨hf', hni'⟩ := b3Unimod_floor_of_mem' h1 h2
    have hRx : b3Unimod_R g g' x = m := by
      rw [b3Unimod_R_of_not_int hni, hf]
    have hRt : b3Unimod_R g g' t = m := by
      rw [b3Unimod_R_of_not_int hni', hf']
    have hJ := b3Unimod_J_eq_of_no_between g' S (x := x) (t := t) fun s hs ⟨h1, h2⟩ ↦ by
      have := hnoS x hxb s hs h1 h2
      exact htS (this ▸ hs)
    rw [hRx, hRt, hJ]

omit hg' in
theorem b3Unimod_deriv_periodic {n : ℤ} (hper : ∀ t, g (t + 1) = g t + n) (t : ℝ) :
    g' (t + 1) = g' t := by
  have h1 : HasDerivAt (fun x ↦ g (x + 1)) (g' (t + 1)) t :=
    HasDerivAt.comp_add_const t 1 (hg (t + 1))
  have h2 : HasDerivAt (fun x ↦ g (x + 1)) (g' t) t := by
    have := (hg t).add_const (n : ℝ)
    simp_rw [hper]
    exact this
  exact h1.unique h2

/-- **The degree of `g`**: the signed count of the integer crossings in `[0, 1)` is `n`. -/
theorem b3Unimod_degree {n : ℤ} (hper : ∀ t, g (t + 1) = g t + n)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (∃ m : ℤ, g t = m) → g' t ≠ 0)
    (hfin : {t | t ∈ Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, g t = m}.Finite) :
    ∑ᶠ t ∈ {t | t ∈ Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, g t = m},
      ((SignType.sign (g' t) : SignType) : ℤ) = n := by
  classical
  set A := {t | t ∈ Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, g t = m}
  set B := {t | t ∈ Ioc (0 : ℝ) 1 ∧ ∃ m : ℤ, g t = m}
  have hg'per := b3Unimod_deriv_periodic hg hper
  -- the bijection `0 ↦ 1` between the crossings in `[0, 1)` and in `(0, 1]`
  set e : ℝ → ℝ := fun t ↦ if t = 0 then 1 else t
  have hint1 : ∀ t, (∃ m : ℤ, g (t + 1) = m) ↔ ∃ m : ℤ, g t = m := fun t ↦ by
    rw [hper]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m - n, by push_cast; linarith⟩
    · rintro ⟨m, hm⟩; exact ⟨m + n, by push_cast; linarith⟩
  have hbij : BijOn e A B := by
    refine ⟨fun t ht ↦ ?_, fun t ht t' ht' h ↦ ?_, fun t ht ↦ ?_⟩
    · by_cases h0 : t = 0
      · simp only [e, ite_eq_left h0]
        refine ⟨⟨one_pos, le_rfl⟩, ?_⟩
        have := (hint1 0).2 (h0 ▸ ht.2)
        simpa using this
      · simp only [e, ite_eq_right h0]
        exact ⟨⟨lt_of_le_of_ne ht.1.1 (Ne.symm h0), ht.1.2.le⟩, ht.2⟩
    · simp only [e] at h
      have h1 := ht.1.2
      have h1' := ht'.1.2
      split_ifs at h with h0 h0' h0' <;> first | exact h0.trans h0'.symm | linarith
    · by_cases h1 : t = 1
      · refine ⟨0, ⟨⟨le_rfl, one_pos⟩, ?_⟩, by simp [e, h1]⟩
        have := (hint1 0).1 (by simpa [h1] using ht.2)
        exact this
      · refine ⟨t, ⟨⟨ht.1.1.le, lt_of_le_of_ne ht.1.2 h1⟩, ht.2⟩, ?_⟩
        simp [e, ht.1.1.ne']
  have hBfin : B.Finite := hbij.image_eq ▸ hfin.image e
  rw [finsum_mem_eq_of_bijOn e hbij (g := fun t ↦ ((SignType.sign (g' t) : SignType) : ℤ))
    fun t _ ↦ by
      simp only [e]
      split_ifs with h0
      · rw [h0, show (1 : ℝ) = 0 + 1 by ring, hg'per]
      · rfl]
  set S := hBfin.toFinset
  have hS : ∀ s, s ∈ S ↔ s ∈ Ioc (0 : ℝ) 1 ∧ ∃ m : ℤ, g s = m := fun s ↦ by
    simp [S, B]
  rw [finsum_mem_eq_finite_toFinset_sum _ hBfin]
  -- `R - J` is constant on `[0, 1]`
  have hcont : ContinuousOn (fun x ↦ b3Unimod_R g g' x - b3Unimod_J g' S x) (Icc (0 : ℝ) 1) := by
    intro t ht
    have := b3Unimod_locallyConst hg hg' S hS hreg ht
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [this] with x hx hxI
    exact (hx hxI).symm
  have hconst := isPreconnected_Icc.constant hcont (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩
  have hJ0 : b3Unimod_J g' S 0 = 0 := by
    unfold b3Unimod_J
    refine Finset.sum_eq_zero fun s hs ↦ ?_
    rw [Finset.mem_filter, hS] at hs
    exact absurd hs.2 (not_le.2 hs.1.1.1)
  have hJ1 : b3Unimod_J g' S 1 = ∑ s ∈ S, ((SignType.sign (g' s) : SignType) : ℤ) := by
    unfold b3Unimod_J
    congr 1
    exact Finset.filter_true_of_mem fun s hs ↦ ((hS s).1 hs).1.2
  have hR1 : b3Unimod_R g g' 1 = b3Unimod_R g g' 0 + n := by
    unfold b3Unimod_R
    have e1 : g 1 = g 0 + n := by simpa using hper 0
    have e2 : g' 1 = g' 0 := by simpa using hg'per 0
    have e3 := hint1 0
    simp only [zero_add] at e3
    rw [e3, e2, e1]
    have : ⌊g 0 + (n : ℝ)⌋ = ⌊g 0⌋ + n := Int.floor_add_intCast _ _
    split_ifs <;> omega
  rw [hJ0, hJ1, hR1] at hconst
  linarith

end Degree

/-! ## A regular level -/

/-- **A common regular level** for finitely many `C¹` functions, outside a countable set. -/
theorem b3Unimod_exists_regular {k : ℕ} (F F' : Fin k → ℝ → ℝ)
    (hF : ∀ j t, HasDerivAt (F j) (F' j t) t) {A : Set ℝ} (hA : A.Countable) :
    ∃ c : ℝ, c ∉ A ∧ ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, ∀ m : ℤ, F j t = c + m → F' j t ≠ 0 := by
  set K : Fin k → Set ℝ := fun j ↦ {t | t ∈ Icc (0 : ℝ) 1 ∧ F' j t = 0}
  have hK : ∀ j, volume (F j '' K j) = 0 := fun j ↦ by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun t ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F' j t))
      (fun t _ ↦ (hF j t).hasFDerivAt.hasFDerivWithinAt) fun t ht ↦ ?_
    rw [ht.2]
    simp
  set Bad : Set ℝ := A ∪ ⋃ j, ⋃ m : ℤ, (fun y ↦ y + (m : ℝ)) ⁻¹' (F j '' K j)
  have hBad : volume Bad = 0 := by
    refine measure_union_null (hA.measure_zero volume) (measure_iUnion_null fun j ↦
      measure_iUnion_null fun m ↦ ?_)
    rw [measure_preimage_add_right]
    exact hK j
  have : Bad ≠ univ := by
    intro h
    rw [h, Real.volume_univ] at hBad
    exact ENNReal.top_ne_zero hBad
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 this
  refine ⟨c, fun h ↦ hc (Or.inl h), fun j t ht m hm h0 ↦ hc (Or.inr ?_)⟩
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨m, ?_⟩⟩
  show c + (m : ℝ) ∈ F j '' K j
  exact ⟨t, ⟨ht, h0⟩, hm⟩

end HodgeLean.Foundations.Program
