import HodgeLean.Foundations.Program.PrymParabolicMarkedLoopsDefs
import Mathlib.Analysis.Convex.PathConnected

/-! # Proofs for stage H3c: the oriented base decomposition and the endpoint monodromy

The `_aux` theorems that `PrymParabolicMarkedLoops.lean` restates, with geometric and
covering-space arguments.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Complex

namespace HodgeLean.Foundations.Program

theorem hg3_arc_im (i : Fin 13) (s : ℝ) :
    (hg3_arc i s).im = 10 - 20 * s := by
  simp only [hg3_arc, mr_basePoint, hg3_bottom, mr_centre, add_im, mul_im, ofReal_re,
    ofReal_im, sub_im, sub_re, add_re, mul_re, I_re, I_im, div_ofNat_re, div_ofNat_im]
  norm_num
  rcases le_total s (1 / 2) with h | h
  · rw [min_eq_left h, max_eq_right h]; ring
  · rw [min_eq_right h, max_eq_left h]; ring

theorem hg3_waist_injective : Function.Injective hg3_waist := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [hg3_waist] at h

theorem hg3_arc_re (i : Fin 13) (s : ℝ) :
    (hg3_arc i s).re = hg3_profile i (10 - 20 * s) := by
  simp only [hg3_arc, hg3_profile, mr_basePoint, hg3_bottom, mr_centre, add_re, mul_re,
    ofReal_re, ofReal_im, sub_re, sub_im, add_im, mul_im, I_re, I_im,
    div_ofNat_re, div_ofNat_im]
  norm_num
  rcases le_total s (1 / 2) with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonneg (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left h, abs_of_nonpos (by linarith)]
    ring

theorem hg3_waist_bound (i : Fin 13) : |hg3_waist i + 11 / 2| ≤ 7 := by
  fin_cases i <;> norm_num [hg3_waist]

theorem hg3_waist_gap (i : Fin 13) (j : Fin 12) :
    1 / 2 ≤ |hg3_waist i - mr_pos j| := by
  fin_cases i <;> fin_cases j <;> norm_num [hg3_waist, mr_pos, mr_int]

theorem hg3_arc_re_bound (i : Fin 13) (s : ℝ) :
    |(hg3_arc i s).re - hg3_waist i| ≤ 7 / 10 * |(hg3_arc i s).im| := by
  rw [hg3_arc_re, hg3_arc_im]
  have he : hg3_profile i (10 - 20 * s) - hg3_waist i =
      -(hg3_waist i + 11 / 2) * |10 - 20 * s| / 10 := by
    unfold hg3_profile
    ring
  rw [he, abs_div, abs_mul, abs_neg, abs_abs]
  norm_num
  have hh := mul_le_mul_of_nonneg_right (hg3_waist_bound i) (abs_nonneg (10 - 20 * s))
  linarith

theorem hg3_arc_far (i : Fin 13) (s : ℝ) (j : Fin 12) (z : ℂ)
    (hre : |z.re - mr_pos j| < 1 / 8) (him : |z.im| < 1 / 8) :
    hg3_arc i s ≠ z := by
  intro h
  have hb := hg3_arc_re_bound i s
  rw [h] at hb
  have hh := hg3_waist_gap i j
  have ht : |hg3_waist i - mr_pos j| ≤
      |z.re - hg3_waist i| + |z.re - mr_pos j| := by
    calc
      _ = |-(z.re - hg3_waist i) + (z.re - mr_pos j)| := by congr 1; ring
      _ ≤ _ := by
        simpa only [abs_neg] using abs_add_le (-(z.re - hg3_waist i)) (z.re - mr_pos j)
  linarith

theorem hg3_arc_avoids_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ (i : Fin 13) (s : unitInterval),
      ((hg3_arc i s : ℂ) : OnePoint ℂ) ∉ Set.range (b6_branch t) ∧
        ((hg3_arc i s : ℂ) : OnePoint ℂ) ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
          Metric.closedBall (mr_base k) (b6t_radius mr_base) := by
  intro i s
  constructor
  · rw [mr_mem_branch]
    rintro (h | ⟨j, h⟩)
    · exact OnePoint.coe_ne_infty _ h
    · have hh := mr_fin_near_parts t ht j
      exact hg3_arc_far i s j (mr_fin t j) hh.1 hh.2 (OnePoint.coe_injective h)
  · simp only [Set.mem_iUnion, not_exists]
    intro k
    rintro ⟨z, hz, he⟩
    have he' : z = hg3_arc i s := OnePoint.coe_injective he
    have hn : ‖z - mr_base k‖ < 1 / 8 :=
      lt_of_le_of_lt (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) mr_radius_lt8
    let j : Fin 12 := ⟨k.val, by omega⟩
    have hm : mr_base k = ((mr_pos j : ℝ) : ℂ) := by
      rw [mr_base_eq, mr_pos]
      rfl
    rw [hm] at hn
    have hr : |z.re - mr_pos j| < 1 / 8 := by
      have hh := Complex.abs_re_le_norm (z - ((mr_pos j : ℝ) : ℂ))
      simp only [sub_re, ofReal_re] at hh
      exact lt_of_le_of_lt hh hn
    have hi : |z.im| < 1 / 8 := by
      have hh := Complex.abs_im_le_norm (z - ((mr_pos j : ℝ) : ℂ))
      simp only [sub_im, ofReal_im, sub_zero] at hh
      exact lt_of_le_of_lt hh hn
    exact hg3_arc_far i s j z hr hi he'.symm

theorem hg3_arc_existsUnique_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ y₁ : b6t_punctured t) (hy₀ : (y₀ : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ))
    (hy₁ : (y₁ : OnePoint ℂ) = ((hg3_bottom : ℂ) : OnePoint ℂ)) (i : Fin 13) :
    ∃! F : Path y₀ y₁, ∀ s : unitInterval, (F s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ) := by
  have hcont : Continuous (hg3_arc i) := by
    unfold hg3_arc
    fun_prop
  have h1 : hg3_arc i 1 = hg3_bottom := by
    have e1 : min (1 : ℝ) (1 / 2) = 1 / 2 := by norm_num
    have e2 : max (1 : ℝ) (1 / 2) = 1 := by norm_num
    simp only [hg3_arc, e1, e2]
    push_cast
    ring
  let F : Path y₀ y₁ :=
    ⟨⟨fun s ↦ ⟨_, (hg3_arc_avoids_aux t ht i s).1⟩,
      (OnePoint.continuous_coe.comp (hcont.comp continuous_subtype_val)).subtype_mk _⟩,
      Subtype.ext (by simpa [hg3_arc] using hy₀.symm),
      Subtype.ext (by simpa [h1] using hy₁.symm)⟩
  refine ⟨F, fun s ↦ rfl, ?_⟩
  intro F' hF'
  apply Path.ext
  funext s
  exact Subtype.ext (hF' s)

theorem hg3_arc_interiors_aux (i j : Fin 13) (s s' : unitInterval)
    (h : hg3_arc i s = hg3_arc j s') :
    (i = j ∧ s = s') ∨ (s = 0 ∧ s' = 0) ∨ (s = 1 ∧ s' = 1) := by
  have he : (s : ℝ) = (s' : ℝ) := by
    have hh := congrArg Complex.im h
    rw [hg3_arc_im, hg3_arc_im] at hh
    linarith
  have hs : s = s' := Subtype.ext he
  subst s'
  by_cases h0 : s = 0
  · exact Or.inr (Or.inl ⟨h0, h0⟩)
  by_cases h1 : s = 1
  · exact Or.inr (Or.inr ⟨h1, h1⟩)
  refine Or.inl ⟨hg3_waist_injective ?_, rfl⟩
  have hp : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1 (by
    intro hh; exact h0 (Subtype.ext hh.symm))
  have hq : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 (by
    intro hh; exact h1 (Subtype.ext hh))
  have hr := congrArg Complex.re h
  simp only [hg3_arc, mr_basePoint, hg3_bottom, mr_centre, add_re, mul_re, ofReal_re,
    ofReal_im, sub_re, sub_im, add_im, mul_im, I_re, I_im, div_ofNat_re, div_ofNat_im] at hr
  norm_num at hr
  rcases le_total (s : ℝ) (1 / 2) with hh | hh
  · rw [min_eq_left hh, max_eq_right hh] at hr
    nlinarith
  · rw [min_eq_right hh, max_eq_left hh] at hr
    nlinarith

theorem hg3_arcSet_iff (i : Fin 13) (z : ℂ) :
    (z : OnePoint ℂ) ∈ hg3_arcSet i ↔
      |z.im| ≤ 10 ∧ z.re = hg3_profile i z.im := by
  constructor
  · rintro ⟨s, hs, he⟩
    have he' := OnePoint.coe_injective he
    subst z
    rw [hg3_arc_im, hg3_arc_re]
    exact ⟨abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
  · rintro ⟨hy, hx⟩
    refine ⟨(10 - z.im) / 20, ⟨?_, ?_⟩, ?_⟩
    · linarith [(abs_le.mp hy).2]
    · linarith [(abs_le.mp hy).1]
    apply congrArg ((↑) : ℂ → OnePoint ℂ)
    apply Complex.ext
    · rw [hg3_arc_re]
      convert hx.symm using 2 <;> ring
    · rw [hg3_arc_im]
      ring

theorem hg3_waist_strictMono : StrictMono hg3_waist := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [hg3_waist] at hij <;> norm_num [hg3_waist]

theorem hg3_profile_strictMono (y : ℝ) (hy : |y| < 10) :
    StrictMono (fun i ↦ hg3_profile i y) := by
  intro i j hij
  have hw := hg3_waist_strictMono hij
  unfold hg3_profile
  nlinarith

theorem hg3_sector_coe_iff (i : Fin 13) (z : ℂ) :
    (z : OnePoint ℂ) ∈ hg3_sector i ↔
      if i.val < 12 then |z.im| < 10 ∧ hg3_profile i z.im < z.re ∧
        z.re < hg3_profile (finRotate 13 i) z.im
      else z ∉ hg3_fan := by
  unfold hg3_sector
  split_ifs <;> simp

theorem hg3_sector_unique (z : OnePoint ℂ) (i j : Fin 13)
    (hi : z ∈ hg3_sector i) (hj : z ∈ hg3_sector j) : i = j := by
  induction z using OnePoint.rec with
  | infty =>
    have h (k : Fin 13) (hk : OnePoint.infty ∈ hg3_sector k) : k = 12 := by
      by_cases hh : k.val < 12
      · simp [hg3_sector, hh] at hk
      · apply Fin.ext; simp; omega
    exact (h i hi).trans (h j hj).symm
  | coe z =>
    rw [hg3_sector_coe_iff] at hi hj
    by_cases hi' : i.val < 12 <;> by_cases hj' : j.val < 12
    · rw [if_pos hi'] at hi
      rw [if_pos hj'] at hj
      have hm := hg3_profile_strictMono z.im hi.1
      have hri : (finRotate 13 i).val = i.val + 1 := by
        rw [hg_finRotate_val]; simp; omega
      have hrj : (finRotate 13 j).val = j.val + 1 := by
        rw [hg_finRotate_val]; simp; omega
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hh | hh
      · have hle : finRotate 13 i ≤ j := by apply Fin.le_iff_val_le_val.mpr; omega
        have hp := hm.monotone hle
        linarith [hi.2.2, hj.2.1]
      · have hle : finRotate 13 j ≤ i := by apply Fin.le_iff_val_le_val.mpr; omega
        have hp := hm.monotone hle
        linarith [hj.2.2, hi.2.1]
    · rw [if_pos hi'] at hi
      rw [if_neg hj'] at hj
      have hm := (hg3_profile_strictMono z.im hi.1).monotone
      exact False.elim (hj ⟨hi.1.le,
        (hm (show (0 : Fin 13) ≤ i by simp)).trans hi.2.1.le,
        hi.2.2.le.trans (hm (show finRotate 13 i ≤ (12 : Fin 13) by omega))⟩)
    · rw [if_neg hi'] at hi
      rw [if_pos hj'] at hj
      have hm := (hg3_profile_strictMono z.im hj.1).monotone
      exact False.elim (hi ⟨hj.1.le,
        (hm (show (0 : Fin 13) ≤ j by simp)).trans hj.2.1.le,
        hj.2.2.le.trans (hm (show finRotate 13 j ≤ (12 : Fin 13) by omega))⟩)
    · apply Fin.ext
      omega

theorem hg3_profile_monotone (y : ℝ) (hy : |y| ≤ 10) :
    Monotone (fun i ↦ hg3_profile i y) := by
  intro i j hij
  have hw := hg3_waist_strictMono.monotone hij
  unfold hg3_profile
  nlinarith

theorem hg3_sector_avoids_arcs (z : OnePoint ℂ) (i : Fin 13) (hi : z ∈ hg3_sector i) :
    z ∉ ⋃ k, hg3_arcSet k := by
  induction z using OnePoint.rec with
  | infty => simp [hg3_arcSet]
  | coe z =>
    rw [hg3_sector_coe_iff] at hi
    simp only [Set.mem_iUnion, not_exists]
    intro k hk
    rw [hg3_arcSet_iff] at hk
    have hm := hg3_profile_monotone z.im hk.1
    by_cases hi' : i.val < 12
    · rw [if_pos hi'] at hi
      by_cases hki : k ≤ i
      · have hh := hm hki
        linarith [hi.2.1, hk.2]
      · have hrot : (finRotate 13 i).val = i.val + 1 := by
          rw [hg_finRotate_val]; simp; omega
        have hh := hm (show finRotate 13 i ≤ k by
          apply Fin.le_iff_val_le_val.mpr; simp only [Fin.le_iff_val_le_val] at hki; omega)
        linarith [hi.2.2, hk.2]
    · rw [if_neg hi'] at hi
      exact hi ⟨hk.1, hk.2 ▸ hm (show (0 : Fin 13) ≤ k by simp),
        hk.2 ▸ hm (show k ≤ (12 : Fin 13) by omega)⟩

theorem hg3_sector_exists (z : OnePoint ℂ) (hz : z ∉ ⋃ k, hg3_arcSet k) :
    ∃ i, z ∈ hg3_sector i := by
  induction z using OnePoint.rec with
  | infty => exact ⟨12, by simp [hg3_sector]⟩
  | coe z =>
    by_cases hf : z ∈ hg3_fan
    · have hne (k : Fin 13) : z.re ≠ hg3_profile k z.im := by
        intro he
        apply hz
        exact Set.mem_iUnion.mpr ⟨k, (hg3_arcSet_iff k z).mpr ⟨hf.1, he⟩⟩
      have hy : |z.im| < 10 := by
        apply lt_of_le_of_ne hf.1
        intro he
        have hp (k : Fin 13) : hg3_profile k z.im = -11 / 2 := by
          simp [hg3_profile, he]
        have hx : z.re = hg3_profile 0 z.im := by
          have h0 := hf.2.1
          have h12 := hf.2.2
          rw [hp 0] at h0
          rw [hp 12] at h12
          rw [hp 0]
          linarith
        exact hne 0 hx
      have h0 : hg3_profile 0 z.im < z.re :=
        lt_of_le_of_ne hf.2.1 (hne 0).symm
      have h12 : z.re < hg3_profile 12 z.im :=
        lt_of_le_of_ne hf.2.2 (hne 12)
      by_cases h1 : z.re < hg3_profile 1 z.im
      · refine ⟨0, ?_⟩
        rw [hg3_sector_coe_iff, if_pos (by decide)]
        exact ⟨hy, h0, h1⟩
      · have h1 : hg3_profile 1 z.im < z.re :=
          lt_of_le_of_ne (le_of_not_gt h1) (hne 1).symm
        by_cases h2 : z.re < hg3_profile 2 z.im
        · refine ⟨1, ?_⟩
          rw [hg3_sector_coe_iff, if_pos (by decide)]
          exact ⟨hy, h1, h2⟩
        · have h2 : hg3_profile 2 z.im < z.re :=
            lt_of_le_of_ne (le_of_not_gt h2) (hne 2).symm
          by_cases h3 : z.re < hg3_profile 3 z.im
          · refine ⟨2, ?_⟩
            rw [hg3_sector_coe_iff, if_pos (by decide)]
            exact ⟨hy, h2, h3⟩
          · have h3 : hg3_profile 3 z.im < z.re :=
              lt_of_le_of_ne (le_of_not_gt h3) (hne 3).symm
            by_cases h4 : z.re < hg3_profile 4 z.im
            · refine ⟨3, ?_⟩
              rw [hg3_sector_coe_iff, if_pos (by decide)]
              exact ⟨hy, h3, h4⟩
            · have h4 : hg3_profile 4 z.im < z.re :=
                lt_of_le_of_ne (le_of_not_gt h4) (hne 4).symm
              by_cases h5 : z.re < hg3_profile 5 z.im
              · refine ⟨4, ?_⟩
                rw [hg3_sector_coe_iff, if_pos (by decide)]
                exact ⟨hy, h4, h5⟩
              · have h5 : hg3_profile 5 z.im < z.re :=
                  lt_of_le_of_ne (le_of_not_gt h5) (hne 5).symm
                by_cases h6 : z.re < hg3_profile 6 z.im
                · refine ⟨5, ?_⟩
                  rw [hg3_sector_coe_iff, if_pos (by decide)]
                  exact ⟨hy, h5, h6⟩
                · have h6 : hg3_profile 6 z.im < z.re :=
                    lt_of_le_of_ne (le_of_not_gt h6) (hne 6).symm
                  by_cases h7 : z.re < hg3_profile 7 z.im
                  · refine ⟨6, ?_⟩
                    rw [hg3_sector_coe_iff, if_pos (by decide)]
                    exact ⟨hy, h6, h7⟩
                  · have h7 : hg3_profile 7 z.im < z.re :=
                      lt_of_le_of_ne (le_of_not_gt h7) (hne 7).symm
                    by_cases h8 : z.re < hg3_profile 8 z.im
                    · refine ⟨7, ?_⟩
                      rw [hg3_sector_coe_iff, if_pos (by decide)]
                      exact ⟨hy, h7, h8⟩
                    · have h8 : hg3_profile 8 z.im < z.re :=
                        lt_of_le_of_ne (le_of_not_gt h8) (hne 8).symm
                      by_cases h9 : z.re < hg3_profile 9 z.im
                      · refine ⟨8, ?_⟩
                        rw [hg3_sector_coe_iff, if_pos (by decide)]
                        exact ⟨hy, h8, h9⟩
                      · have h9 : hg3_profile 9 z.im < z.re :=
                          lt_of_le_of_ne (le_of_not_gt h9) (hne 9).symm
                        by_cases h10 : z.re < hg3_profile 10 z.im
                        · refine ⟨9, ?_⟩
                          rw [hg3_sector_coe_iff, if_pos (by decide)]
                          exact ⟨hy, h9, h10⟩
                        · have h10 : hg3_profile 10 z.im < z.re :=
                            lt_of_le_of_ne (le_of_not_gt h10) (hne 10).symm
                          by_cases h11 : z.re < hg3_profile 11 z.im
                          · refine ⟨10, ?_⟩
                            rw [hg3_sector_coe_iff, if_pos (by decide)]
                            exact ⟨hy, h10, h11⟩
                          · have h11 : hg3_profile 11 z.im < z.re :=
                              lt_of_le_of_ne (le_of_not_gt h11) (hne 11).symm
                            exact ⟨11, by
                              rw [hg3_sector_coe_iff, if_pos (by decide)]
                              exact ⟨hy, h11, h12⟩⟩
    · exact ⟨12, (hg3_sector_coe_iff 12 z).mpr (by simpa using hf)⟩

theorem hg3_sector_partition_aux (z : OnePoint ℂ) :
    z ∉ ⋃ i, hg3_arcSet i ↔ ∃! i, z ∈ hg3_sector i := by
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := hg3_sector_exists z hz
    exact ⟨i, hi, fun j hj ↦ hg3_sector_unique z j i hj hi⟩
  · rintro ⟨i, hi, _⟩
    exact hg3_sector_avoids_arcs z i hi

theorem hg3_profile_scale (i : Fin 13) (y a b : ℝ)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    hg3_profile i (b * y) = a * hg3_waist i + b * hg3_profile i y := by
  unfold hg3_profile
  rw [abs_mul, abs_of_nonneg hb]
  rw [show a = 1 - b by linarith]
  ring

theorem hg3_finite_sector_connected (i : Fin 13) (hi : i.val < 12) :
    IsConnected {z : ℂ | |z.im| < 10 ∧ hg3_profile i z.im < z.re ∧
      z.re < hg3_profile (finRotate 13 i) z.im} := by
  let m : ℝ := (hg3_waist i + hg3_waist (finRotate 13 i)) / 2
  have hrot : i < finRotate 13 i := by
    rw [Fin.lt_iff_val_lt_val, hg_finRotate_val]
    split_ifs <;> omega
  have hw := hg3_waist_strictMono hrot
  have hm : (m : ℂ) ∈ {z : ℂ | |z.im| < 10 ∧ hg3_profile i z.im < z.re ∧
      z.re < hg3_profile (finRotate 13 i) z.im} := by
    simp only [Set.mem_setOf_eq, ofReal_im, ofReal_re, abs_zero, hg3_profile,
      zero_div, sub_zero, mul_one]
    dsimp [m]
    constructor
    · norm_num
    · constructor <;> linarith
  have hs : StarConvex ℝ (m : ℂ) {z : ℂ | |z.im| < 10 ∧
      hg3_profile i z.im < z.re ∧ z.re < hg3_profile (finRotate 13 i) z.im} := by
    intro z hz a b ha hb hab
    simp only [Set.mem_setOf_eq, add_im, add_re, smul_im, smul_re, smul_eq_mul,
      ofReal_im, ofReal_re, mul_zero, zero_add]
    rw [hg3_profile_scale i z.im a b hb hab,
      hg3_profile_scale (finRotate 13 i) z.im a b hb hab, abs_mul, abs_of_nonneg hb]
    change |z.im| < 10 ∧ hg3_profile i z.im < z.re ∧
      z.re < hg3_profile (finRotate 13 i) z.im at hz
    have hba : b ≤ 1 := by linarith
    have hm1 : hg3_waist i < m := by dsimp [m]; linarith
    have hm2 : m < hg3_waist (finRotate 13 i) := by dsimp [m]; linarith
    constructor
    · nlinarith [abs_nonneg z.im]
    · constructor
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simpa [ha0, hb1] using hz.2.1
        · nlinarith [mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (sub_pos.mpr hm1),
            mul_nonneg hb (sub_nonneg.mpr hz.2.1.le)]
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simpa [ha0, hb1] using hz.2.2
        · nlinarith [mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (sub_pos.mpr hm2),
            mul_nonneg hb (sub_nonneg.mpr hz.2.2.le)]
  exact (hs.isPathConnected hm).isConnected

theorem hg3_finite_sector_open (i : Fin 13) :
    IsOpen {z : ℂ | |z.im| < 10 ∧ hg3_profile i z.im < z.re ∧
      z.re < hg3_profile (finRotate 13 i) z.im} := by
  have hc (j : Fin 13) : Continuous (fun z : ℂ ↦ hg3_profile j z.im) := by
    unfold hg3_profile
    fun_prop
  exact (isOpen_lt (continuous_abs.comp continuous_im) continuous_const).inter
    ((isOpen_lt (hc i) continuous_re).inter
      (isOpen_lt continuous_re (hc (finRotate 13 i))))

theorem hg3_fan_iff (z : ℂ) :
    z ∈ hg3_fan ↔ |z.re + 11 / 2| / 7 + |z.im| / 10 ≤ 1 := by
  have he0 : hg3_profile 0 z.im = -11 / 2 - 7 * (1 - |z.im| / 10) := by
    norm_num [hg3_profile, hg3_waist]; ring
  have he12 : hg3_profile 12 z.im = -11 / 2 + 7 * (1 - |z.im| / 10) := by
    norm_num [hg3_profile, hg3_waist]
  change (|z.im| ≤ 10 ∧ hg3_profile 0 z.im ≤ z.re ∧
    z.re ≤ hg3_profile 12 z.im) ↔ _
  rw [he0, he12]
  constructor
  · intro h
    have hx : |z.re + 11 / 2| ≤ 7 * (1 - |z.im| / 10) := by
      rw [abs_le]; constructor <;> linarith [h.2.1, h.2.2]
    linarith
  · intro h
    have hy : |z.im| ≤ 10 := by linarith [abs_nonneg (z.re + 11 / 2)]
    have hx : |z.re + 11 / 2| ≤ 7 * (1 - |z.im| / 10) := by linarith
    have hx' := abs_le.mp hx
    exact ⟨hy, by linarith [hx'.1], by linarith [hx'.2]⟩

theorem hg3_fan_compact : IsCompact hg3_fan := by
  have hc : Continuous (fun z : ℂ ↦ |z.re + 11 / 2| / 7 + |z.im| / 10) := by fun_prop
  have he : hg3_fan = {z : ℂ | |z.re + 11 / 2| / 7 + |z.im| / 10 ≤ 1} :=
    Set.ext hg3_fan_iff
  have hcl : IsClosed hg3_fan := by rw [he]; exact isClosed_le hc continuous_const
  apply (isCompact_closedBall (0 : ℂ) 30).of_isClosed_subset hcl
  intro z hz
  have hy := hz.1
  have hx := (hg3_fan_iff z).mp hz
  have hx' : |z.re + 11 / 2| ≤ 7 := by linarith [abs_nonneg z.im]
  have hr : |z.re| ≤ 25 / 2 := by
    have hh := abs_add_le (z.re + 11 / 2) (-11 / 2)
    norm_num at hh
    have he' : z.re + 11 / 2 + -11 / 2 = z.re := by ring
    linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn := Complex.norm_le_abs_re_add_abs_im z
  linarith

theorem hg3_infty_ray (c v : ℂ) (hv : v ≠ 0) :
    OnePoint.infty ∈ closure ((fun r : ℝ ↦ ((c + r • v : ℂ) : OnePoint ℂ)) ''
      Set.Ici 1) := by
  by_contra hh
  have hc := ((OnePoint.isClosed_iff_of_notMem hh).mp isClosed_closure).2
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r : ℝ := max 1 ((B + ‖c‖ + 1) / ‖v‖)
  have hr : 1 ≤ r := le_max_left _ _
  have hrv : B + ‖c‖ + 1 ≤ r * ‖v‖ :=
    (div_le_iff₀ hn).mp (le_max_right _ _)
  have hmem : ((c + r • v : ℂ) : OnePoint ℂ) ∈ closure
      ((fun r : ℝ ↦ ((c + r • v : ℂ) : OnePoint ℂ)) '' Set.Ici 1) :=
    subset_closure ⟨r, hr, rfl⟩
  have hb := hB (c + r • v) hmem
  have ht : ‖r • v‖ ≤ ‖c + r • v‖ + ‖c‖ := by
    have ht := norm_sub_le (c + r • v) c
    simpa only [add_sub_cancel_left] using ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r)] at ht
  linarith

theorem hg3_ray_connected (c v : ℂ) (hv : v ≠ 0) :
    IsConnected (insert OnePoint.infty
      ((fun r : ℝ ↦ ((c + r • v : ℂ) : OnePoint ℂ)) '' Set.Ici 1)) := by
  have hc := (isConnected_Ici (a := (1 : ℝ))).image (fun r : ℝ ↦
    ((c + r • v : ℂ) : OnePoint ℂ))
    (OnePoint.continuous_coe.comp (by fun_prop)).continuousOn
  apply hc.subset_closure (Set.subset_insert _ _)
  exact Set.insert_subset (hg3_infty_ray c v hv) subset_closure

theorem hg3_exterior_connected :
    IsConnected ((((↑) : ℂ → OnePoint ℂ) '' hg3_fan)ᶜ) := by
  refine ⟨⟨OnePoint.infty, by simp⟩, isPreconnected_of_forall OnePoint.infty ?_⟩
  intro y hy
  induction y using OnePoint.rec with
  | infty =>
    exact ⟨{OnePoint.infty}, by simpa using hy, by simp, by simp,
      isPreconnected_singleton⟩
  | coe z =>
    have hz : z ∉ hg3_fan := by simpa using hy
    have hG : 1 < |z.re + 11 / 2| / 7 + |z.im| / 10 :=
      lt_of_not_ge (fun h ↦ hz ((hg3_fan_iff z).mpr h))
    have hv : z - (mr_centre : ℂ) ≠ 0 := by
      intro he
      have he' := sub_eq_zero.mp he
      subst z
      norm_num [mr_centre] at hG
    refine ⟨insert OnePoint.infty
      ((fun r : ℝ ↦ (((mr_centre : ℂ) + r • (z - mr_centre) : ℂ) : OnePoint ℂ)) ''
        Set.Ici 1), ?_, Set.mem_insert _ _, ?_,
      (hg3_ray_connected mr_centre (z - mr_centre) hv).isPreconnected⟩
    · intro w hw
      rcases hw with rfl | ⟨r, hr, rfl⟩
      · simp
      · change 1 ≤ r at hr
        have he : |((mr_centre : ℂ) + r • (z - mr_centre)).re + 11 / 2| / 7 +
            |((mr_centre : ℂ) + r • (z - mr_centre)).im| / 10 =
            r * (|z.re + 11 / 2| / 7 + |z.im| / 10) := by
          have h1 : ((mr_centre : ℂ) + r • (z - mr_centre)).re + 11 / 2 =
              r * (z.re + 11 / 2) := by simp [mr_centre, smul_re]; ring
          have h2 : ((mr_centre : ℂ) + r • (z - mr_centre)).im = r * z.im := by
            simp [mr_centre, smul_im]
          rw [h1, h2, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ r)]
          ring
        have hnot : (mr_centre : ℂ) + r • (z - mr_centre) ∉ hg3_fan := by
          rw [hg3_fan_iff, he]
          nlinarith
        simpa using hnot
    · apply Set.mem_insert_of_mem
      refine ⟨1, by simp, ?_⟩
      simp

theorem hg3_sector_open_connected_aux (i : Fin 13) :
    IsOpen (hg3_sector i) ∧ IsConnected (hg3_sector i) := by
  by_cases hi : i.val < 12
  · rw [hg3_sector, if_pos hi]
    exact ⟨OnePoint.isOpen_image_coe.mpr (hg3_finite_sector_open i),
      (hg3_finite_sector_connected i hi).image _ OnePoint.continuous_coe.continuousOn⟩
  · rw [hg3_sector, if_neg hi]
    exact ⟨(hg3_fan_compact.image OnePoint.continuous_coe).isClosed.isOpen_compl,
      hg3_exterior_connected⟩

theorem hg3_profile_bound (i : Fin 13) (y : ℝ) :
    |hg3_profile i y - hg3_waist i| ≤ 7 / 10 * |y| := by
  have he : hg3_profile i y - hg3_waist i =
      -(hg3_waist i + 11 / 2) * |y| / 10 := by unfold hg3_profile; ring
  rw [he, abs_div, abs_mul, abs_neg, abs_abs]
  norm_num
  have hh := mul_le_mul_of_nonneg_right (hg3_waist_bound i) (abs_nonneg y)
  linarith

theorem hg3_waist_left (i : Fin 13) (j : Fin 12) (h : i.val ≤ j.val) :
    hg3_waist i + 1 / 2 ≤ mr_pos j := by
  fin_cases i <;> fin_cases j <;> norm_num [hg3_waist, mr_pos, mr_int] at h <;> norm_num [hg3_waist, mr_pos, mr_int]

theorem hg3_waist_right (i : Fin 13) (j : Fin 12) (h : j.val < i.val) :
    mr_pos j + 1 / 2 ≤ hg3_waist i := by
  fin_cases i <;> fin_cases j <;> norm_num [hg3_waist, mr_pos, mr_int] at h <;> norm_num [hg3_waist, mr_pos, mr_int]

theorem hg3_mark_profiles (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (i : Fin 13) (j : Fin 12) :
    (hg3_profile i (mr_fin t j).im < (mr_fin t j).re ↔ i.val ≤ j.val) ∧
    ((mr_fin t j).re < hg3_profile i (mr_fin t j).im ↔ j.val < i.val) := by
  have hn := mr_fin_near_parts t ht j
  have hb := hg3_profile_bound i (mr_fin t j).im
  have hbr := (abs_le.mp hb)
  have hnr := (abs_lt.mp hn.1)
  by_cases hij : i.val ≤ j.val
  · have hw := hg3_waist_left i j hij
    have hh : hg3_profile i (mr_fin t j).im < (mr_fin t j).re := by linarith [hn.2]
    exact ⟨iff_of_true hh hij, iff_of_false (not_lt.mpr hh.le) (by omega)⟩
  · have hw := hg3_waist_right i j (by omega)
    have hh : (mr_fin t j).re < hg3_profile i (mr_fin t j).im := by linarith [hn.2]
    exact ⟨iff_of_false (not_lt.mpr hh.le) hij, iff_of_true hh (by omega)⟩

theorem hg3_sector_mark_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) (i j : Fin 13) :
    b6_branch t j ∈ hg3_sector i ↔ j = i := by
  induction j using Fin.lastCases with
  | last =>
    rw [mr_branch_last]
    by_cases hi : i.val < 12
    · simp [hg3_sector, hi]
      intro he
      have := congrArg Fin.val he
      simp at this
      omega
    · have hi' : i = 12 := by apply Fin.ext; simp; omega
      subst i
      simp [hg3_sector]
  | cast j =>
    rw [mr_branch_castSucc]
    have hn := mr_fin_near_parts t ht j
    have hy : |(mr_fin t j).im| < 10 := by linarith [hn.2]
    by_cases hi : i.val < 12
    · have hrot : (finRotate 13 i).val = i.val + 1 := by rw [hg_finRotate_val]; simp; omega
      have hp := hg3_mark_profiles t ht i j
      have hq := hg3_mark_profiles t ht (finRotate 13 i) j
      simp only [hg3_sector, if_pos hi, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, ⟨_, hl, hr⟩, he⟩
        have he' := OnePoint.coe_injective he
        subst z
        have hl' := hp.1.mp hl
        have hr' := hq.2.mp hr
        apply Fin.ext
        simp only [Fin.val_castSucc]
        omega
      · intro he
        have hij : i.val = j.val := by simpa using (congrArg Fin.val he).symm
        refine ⟨mr_fin t j, ⟨hy, hp.1.mpr (by omega), hq.2.mpr (by omega)⟩, rfl⟩
    · have hp := hg3_mark_profiles t ht 0 j
      have hq := hg3_mark_profiles t ht 12 j
      have hm : mr_fin t j ∈ hg3_fan :=
        ⟨hy.le, (hp.1.mpr (by simp)).le, (hq.2.mpr (by simpa using j.isLt)).le⟩
      have hi' : i = 12 := by apply Fin.ext; simp; omega
      subst i
      simp only [hg3_sector, show ¬(12 : Fin 13).val < 12 by decide, if_false,
        Set.mem_compl_iff]
      constructor
      · intro h
        exact False.elim (h ⟨_, hm, rfl⟩)
      · intro he
        have hh := congrArg Fin.val he
        simp at hh
        omega

theorem hg3_arc_cut (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (i : Fin 13) (s : ℝ) (hs : -1 / 4 ≤ (hg3_arc i s).im)
    (j : Fin 12) (he : (hg3_arc i s).re = (mr_fin t j).re) :
    (mr_fin t j).im < (hg3_arc i s).im := by
  by_contra hn
  have hn' := le_of_not_gt hn
  have hm := mr_fin_near_parts t ht j
  have hi : |(hg3_arc i s).im| ≤ 1 / 4 := by
    rw [abs_le]; constructor <;> linarith [(abs_lt.mp hm.2).2]
  have hb := hg3_arc_re_bound i s
  have hw := hg3_waist_gap i j
  have hh : |hg3_waist i - mr_pos j| ≤
      |(hg3_arc i s).re - hg3_waist i| + |(mr_fin t j).re - mr_pos j| := by
    rw [he]
    calc
      _ = |-((mr_fin t j).re - hg3_waist i) + ((mr_fin t j).re - mr_pos j)| := by
        congr 1; ring
      _ ≤ _ := by
        simpa only [abs_neg] using (abs_add_le (-((mr_fin t j).re - hg3_waist i)) ((mr_fin t j).re - mr_pos j))
  linarith [hm.1]

theorem hg3_throat_order (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (i : Fin 13) (j : Fin 12) :
    (hg3_profile i (-1 / 4) < (mr_fin t j).re ↔ i.val ≤ j.val) ∧
    ((mr_fin t j).re < hg3_profile i (-1 / 4) ↔ j.val < i.val) := by
  have hn := mr_fin_near_parts t ht j
  have hb := hg3_profile_bound i (-1 / 4)
  norm_num at hb
  have hbr := abs_le.mp hb
  have hnr := abs_lt.mp hn.1
  by_cases hij : i.val ≤ j.val
  · have hw := hg3_waist_left i j hij
    have hh : hg3_profile i (-1 / 4) < (mr_fin t j).re := by linarith
    exact ⟨iff_of_true hh hij, iff_of_false (not_lt.mpr hh.le) (by omega)⟩
  · have hw := hg3_waist_right i j (by omega)
    have hh : (mr_fin t j).re < hg3_profile i (-1 / 4) := by linarith
    exact ⟨iff_of_false (not_lt.mpr hh.le) hij, iff_of_true hh (by omega)⟩

theorem hg3_upper_join (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (p q : {z : ℂ // z ∉ mr_planeSet t})
    (hp : 1 / 8 ≤ (p : ℂ).im) (hq : 1 / 8 ≤ (q : ℂ).im)
    (hs : ∀ j : Fin 12,
      ((p : ℂ).re < (mr_fin t j).re ∧ (q : ℂ).re < (mr_fin t j).re) ∨
      ((mr_fin t j).re < (p : ℂ).re ∧ (mr_fin t j).re < (q : ℂ).re)) :
    ∃ L : Path p q, ∀ s,
      (∀ b ∈ mr_planeSet t, (L s : ℂ).re = b.re → (L s : ℂ).im < b.im) ∧
      1 / 8 ≤ (L s : ℂ).im := by
  let f (s : unitInterval) : ℂ := (1 - (s : ℝ)) • (p : ℂ) + (s : ℝ) • (q : ℂ)
  have hf (s : unitInterval) : 1 / 8 ≤ (f s).im := by
    dsimp [f]
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [s.property.1, s.property.2]
  have hn (s : unitInterval) : f s ∉ mr_planeSet t := by
    rintro ⟨j, he⟩
    have hm := (abs_lt.mp (mr_fin_near_parts t ht j).2).1
    have hh := congrArg Complex.im he
    simp only [conj_im] at hh
    linarith [hf s]
  let L : Path p q :=
    ⟨⟨fun s ↦ ⟨f s, hn s⟩, by dsimp [f]; fun_prop⟩,
      Subtype.ext (by simp [f]), Subtype.ext (by simp [f])⟩
  refine ⟨L, fun s ↦ ⟨?_, hf s⟩⟩
  rintro _ ⟨j, rfl⟩ he
  change (f s).re = ((starRingEnd ℂ) (mr_fin t j)).re at he
  simp only [conj_re] at he
  have h0 := s.property.1
  have h1 := s.property.2
  dsimp [f] at he
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at he
  rcases hs j with ⟨hpl, hql⟩ | ⟨hpr, hqr⟩
  · by_cases hz : (s : ℝ) = 0
    · simp only [hz, sub_zero, one_mul, zero_mul, add_zero] at he
      exact False.elim ((ne_of_lt hpl) he)
    · exfalso
      nlinarith [mul_pos (lt_of_le_of_ne h0 (Ne.symm hz)) (sub_pos.mpr hql),
        mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hpl.le)]
  · by_cases hz : (s : ℝ) = 0
    · simp only [hz, sub_zero, one_mul, zero_mul, add_zero] at he
      exact False.elim ((ne_of_gt hpr) he)
    · exfalso
      nlinarith [mul_pos (lt_of_le_of_ne h0 (Ne.symm hz)) (sub_pos.mpr hqr),
        mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hpr.le)]

theorem hg3_lasso_low (n : ℝ) (s : ℝ) (h0 : 4 / 9 ≤ s) (h1 : s ≤ 5 / 9) :
    (mr_lasso n s).im ≤ -1 / 8 := by
  obtain ⟨_, him⟩ := mr_lasso_mid n s (by linarith) (by linarith)
  have hc := mr_cos_le (2 * Real.pi * (3 * s - 1))
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [him]
  linarith

theorem hg3_ell_eval (t : Fin 10 → ℂ)
    (Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t})
    (hΨ : ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z →
      (Ψ y : ℂ) = (starRingEnd ℂ) z)
    (y₀ y₁ : b6t_punctured t) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (i : Fin 13) (s : unitInterval) :
    (((((F i).trans (F (finRotate 13 i)).symm).map Ψ.continuous) s : ℂ)) =
      (starRingEnd ℂ) (if (s : ℝ) ≤ 1 / 2 then hg3_arc i (2 * s)
        else hg3_arc (finRotate 13 i) (2 - 2 * s)) := by
  simp only [Path.map_coe, Function.comp_apply, Path.trans_apply]
  split_ifs with hs
  · exact hΨ _ _ (hF i _)
  · let u : unitInterval := ⟨2 * (s : ℝ) - 1, by
      constructor <;> linarith [s.property.2]⟩
    change (Ψ ((F (finRotate 13 i)) (unitInterval.symm u)) : ℂ) = _
    rw [hΨ _ _ (hF (finRotate 13 i) (unitInterval.symm u))]
    congr 2
    change 1 - (2 * (s : ℝ) - 1) = 2 - 2 * s
    ring

theorem hg3_ell_cut (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t})
    (hΨ : ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z →
      (Ψ y : ℂ) = (starRingEnd ℂ) z)
    (y₀ y₁ : b6t_punctured t) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (i : Fin 13) (s : unitInterval)
    (hs : (s : ℝ) ≤ 41 / 160 ∨ 119 / 160 ≤ (s : ℝ)) :
    ∀ b ∈ mr_planeSet t,
      (((((F i).trans (F (finRotate 13 i)).symm).map Ψ.continuous) s : ℂ)).re = b.re →
      (((((F i).trans (F (finRotate 13 i)).symm).map Ψ.continuous) s : ℂ)).im < b.im := by
  rintro _ ⟨j, rfl⟩ he
  rw [hg3_ell_eval t Ψ hΨ y₀ y₁ F hF i s] at he ⊢
  split_ifs at he ⊢ with hh
  · simp only [conj_re, conj_im] at he ⊢
    have him : -1 / 4 ≤ (hg3_arc i (2 * s)).im := by
      rw [hg3_arc_im]
      rcases hs with hs | hs <;> linarith
    linarith [hg3_arc_cut t ht i (2 * s) him j he]
  · simp only [conj_re, conj_im] at he ⊢
    have him : -1 / 4 ≤ (hg3_arc (finRotate 13 i) (2 - 2 * s)).im := by
      rw [hg3_arc_im]
      rcases hs with hs | hs <;> linarith
    linarith [hg3_arc_cut t ht (finRotate 13 i) (2 - 2 * s) him j he]

theorem hg3_ell_low (t : Fin 10 → ℂ)
    (Ψ : b6t_punctured t ≃ₜ {z : ℂ // z ∉ mr_planeSet t})
    (hΨ : ∀ (y : b6t_punctured t) (z : ℂ), (y : OnePoint ℂ) = z →
      (Ψ y : ℂ) = (starRingEnd ℂ) z)
    (y₀ y₁ : b6t_punctured t) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (i : Fin 13) (s : unitInterval) (h0 : 41 / 160 ≤ (s : ℝ))
    (h1 : (s : ℝ) ≤ 119 / 160) :
    1 / 4 ≤ (((((F i).trans (F (finRotate 13 i)).symm).map Ψ.continuous) s : ℂ)).im := by
  rw [hg3_ell_eval t Ψ hΨ y₀ y₁ F hF i s]
  split_ifs <;> rw [conj_im, hg3_arc_im] <;> linarith

theorem hg3_lasso_gap (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (j k : Fin 12) :
    ((hg3_profile j.castSucc (-1 / 4) < (mr_fin t k).re ∧
      (mr_lasso (mr_pos j) (4 / 9)).re < (mr_fin t k).re) ∨
     ((mr_fin t k).re < hg3_profile j.castSucc (-1 / 4) ∧
      (mr_fin t k).re < (mr_lasso (mr_pos j) (4 / 9)).re)) ∧
    ((hg3_profile j.succ (-1 / 4) < (mr_fin t k).re ∧
      (mr_lasso (mr_pos j) (5 / 9)).re < (mr_fin t k).re) ∨
     ((mr_fin t k).re < hg3_profile j.succ (-1 / 4) ∧
      (mr_fin t k).re < (mr_lasso (mr_pos j) (5 / 9)).re)) := by
  have hL := hg3_throat_order t ht j.castSucc k
  have hR := hg3_throat_order t ht j.succ k
  have he := mr_lasso_ends (mr_pos j) (mr_fin t j) (mr_fin_near_parts t ht j).1
  by_cases hkj : k = j
  · subst k
    exact ⟨Or.inl ⟨hL.1.mpr (by simp), he.1⟩,
      Or.inr ⟨hR.2.mpr (by simp), he.2⟩⟩
  have hp := mr_pos_sep k j hkj
  have hm := abs_lt.mp (mr_fin_near_parts t ht k).1
  obtain ⟨heL, _⟩ := mr_lasso_mid (mr_pos j) (4 / 9) (by norm_num) (by norm_num)
  obtain ⟨heR, _⟩ := mr_lasso_mid (mr_pos j) (5 / 9) (by norm_num) (by norm_num)
  have hsl := Real.abs_sin_le_one (2 * Real.pi * (3 * (4 / 9) - 1))
  have hsr := Real.abs_sin_le_one (2 * Real.pi * (3 * (5 / 9) - 1))
  have hsl' := abs_le.mp hsl
  have hsr' := abs_le.mp hsr
  rcases lt_or_gt_of_ne hkj with hkj | hjk
  · have hpos := mr_pos_strictMono hkj
    rw [abs_of_neg (sub_neg.mpr hpos)] at hp
    refine ⟨Or.inr ⟨hL.2.mpr (by exact hkj), ?_⟩,
      Or.inr ⟨hR.2.mpr (by simp; omega), ?_⟩⟩
    · rw [heL]; linarith
    · rw [heR]; linarith
  · have hpos := mr_pos_strictMono hjk
    rw [abs_of_pos (sub_pos.mpr hpos)] at hp
    refine ⟨Or.inl ⟨hL.1.mpr (by exact hjk.le), ?_⟩,
      Or.inl ⟨hR.1.mpr (by simp; omega), ?_⟩⟩
    · rw [heL]; linarith
    · rw [heR]; linarith

theorem hg3_upper_chart_contractible (t : Fin 10 → ℂ)
    (ht : t ∈ b6t_polydisc mr_base) :
    ContractibleSpace {z : {z : ℂ // z ∉ mr_planeSet t} // 1 / 8 ≤ (z : ℂ).im} := by
  let V := {z : ℂ | 1 / 8 ≤ z.im}
  have hv : Convex ℝ V := by
    intro x hx y hy a b ha hb hab
    change 1 / 8 ≤ (a • x + b • y).im
    simp only [add_im, smul_im, smul_eq_mul]
    change 1 / 8 ≤ x.im at hx
    change 1 / 8 ≤ y.im at hy
    nlinarith
  letI : ContractibleSpace V := hv.contractibleSpace ⟨I, by norm_num [V]⟩
  apply RiemannRochTop_contractible_nested_subset V (mr_planeSet t)ᶜ
  intro z hz
  rintro ⟨j, he⟩
  have hh := (abs_lt.mp (mr_fin_near_parts t ht j).2).1
  have he' := congrArg Complex.im he
  simp only [conj_im] at he'
  change 1 / 8 ≤ z.im at hz
  linarith

theorem hg3_ell_finite (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ y₁ : b6t_punctured t) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (j : Fin 12) (P : Path y₀ y₀)
    (hP : ∀ s : unitInterval, (P s : OnePoint ℂ) = mr_curve j.castSucc s) :
    FundamentalGroup.fromPath ⟦(F j.castSucc).trans (F (finRotate 13 j.castSucc)).symm⟧ =
      FundamentalGroup.fromPath ⟦P⟧ := by
  obtain ⟨Ψ, hΨ⟩ := mr_plane_exists t
  let E := ((F j.castSucc).trans (F (finRotate 13 j.castSucc)).symm).map Ψ.continuous
  let C := P.map Ψ.continuous
  let u₁ : unitInterval := ⟨41 / 160, by norm_num, by norm_num⟩
  let u₂ : unitInterval := ⟨119 / 160, by norm_num, by norm_num⟩
  let v₁ : unitInterval := ⟨4 / 9, by norm_num, by norm_num⟩
  let v₂ : unitInterval := ⟨5 / 9, by norm_num, by norm_num⟩
  have hC (s : unitInterval) :
      (C s : ℂ) = (starRingEnd ℂ) (mr_lasso (mr_pos j) s) :=
    hΨ (P s) _ ((hP s).trans (mr_curve_castSucc j s))
  have hrot : finRotate 13 j.castSucc = j.succ := by
    apply Fin.ext
    rw [hg_finRotate_val]
    simp
    omega
  have hLre : (E u₁ : ℂ).re = hg3_profile j.castSucc (-1 / 4) := by
    rw [hg3_ell_eval t Ψ hΨ y₀ y₁ F hF j.castSucc u₁]
    norm_num [u₁]
    rw [hg3_arc_re]
    norm_num
  have hRre : (E u₂ : ℂ).re = hg3_profile j.succ (-1 / 4) := by
    rw [hg3_ell_eval t Ψ hΨ y₀ y₁ F hF j.castSucc u₂]
    norm_num [u₂]
    rw [hg3_arc_re]
    norm_num
  have hLim : 1 / 8 ≤ (E u₁ : ℂ).im := by
    have hh := hg3_ell_low t Ψ hΨ y₀ y₁ F hF j.castSucc u₁ (by rfl) (by norm_num [u₁])
    linarith
  have hRim : 1 / 8 ≤ (E u₂ : ℂ).im := by
    have hh := hg3_ell_low t Ψ hΨ y₀ y₁ F hF j.castSucc u₂ (by norm_num [u₂]) (by rfl)
    linarith
  have hClow (s : unitInterval) (hs0 : v₁ ≤ s) (hs1 : s ≤ v₂) :
      1 / 8 ≤ (C s : ℂ).im := by
    rw [hC, conj_im]
    have hh := hg3_lasso_low (mr_pos j) s hs0 hs1
    linarith
  obtain ⟨L, hL⟩ := hg3_upper_join t ht (E u₁) (C v₁) hLim
    (hClow v₁ (le_refl _) (by norm_num [v₁, v₂])) (fun k ↦ by
      rw [hLre, hC, conj_re]
      exact (hg3_lasso_gap t ht j k).1)
  obtain ⟨R, hR⟩ := hg3_upper_join t ht (E u₂) (C v₂) hRim
    (hClow v₂ (by norm_num [v₁, v₂]) (le_refl _)) (fun k ↦ by
      rw [hRre, hC, conj_re]
      exact (hg3_lasso_gap t ht j k).2)
  obtain ⟨a, d, b, ha, hd, hb, hE⟩ :=
    mr_three_split E u₁ u₂ (by norm_num [u₁, u₂])
  obtain ⟨a', d', b', ha', hd', hb', hC'⟩ :=
    mr_three_split C v₁ v₂ (by norm_num [v₁, v₂])
  let S := {z : {z : ℂ // z ∉ mr_planeSet t} |
    ∀ b ∈ mr_planeSet t, (z : ℂ).re = b.re → (z : ℂ).im < b.im}
  let V := {z : {z : ℂ // z ∉ mr_planeSet t} | 1 / 8 ≤ (z : ℂ).im}
  letI : ContractibleSpace S :=
    (RiemannRochTop_punctured_cut_charts_contractible (mr_planeSet t)
      (mr_planeSet_finite t) ((starRingEnd ℂ) (mr_fin t 0)) (1 / 2) (by norm_num)
      (mr_plane_iso t ht 0)).1
  letI : ContractibleSpace V := hg3_upper_chart_contractible t ht
  have hcoff (s : unitInterval) (hs : s ≤ v₁ ∨ v₂ ≤ s) :
      C s ∈ S := by
    rintro _ ⟨k, rfl⟩ he
    rw [hC] at he ⊢
    simp only [conj_re, conj_im] at he ⊢
    have hm := (mr_fin_re_cases t ht k j).imp (fun h ↦ h.2) (fun h ↦ h.2)
    have hh := mr_lasso_off (mr_pos j) (mr_fin t k) (mr_fin_near_parts t ht k).2
      hm s s.property.1 s.property.2 hs he
    linarith
  have hhom := RiemannRochTop_two_chart_loops_homotopic S V a d b a' d' b' L R
    (fun τ ↦ by
      obtain ⟨s, hs, he⟩ := ha τ
      rw [he]
      exact hg3_ell_cut t ht Ψ hΨ y₀ y₁ F hF j.castSucc s (Or.inl hs))
    (fun τ ↦ by
      obtain ⟨s, hs0, hs1, he⟩ := hd τ
      rw [he]
      have hh := hg3_ell_low t Ψ hΨ y₀ y₁ F hF j.castSucc s hs0 hs1
      change 1 / 8 ≤ (E s : ℂ).im
      linarith)
    (fun τ ↦ by
      obtain ⟨s, hs, he⟩ := hb τ
      rw [he]
      exact hg3_ell_cut t ht Ψ hΨ y₀ y₁ F hF j.castSucc s (Or.inr hs))
    (fun τ ↦ by
      obtain ⟨s, hs, he⟩ := ha' τ
      rw [he]
      exact hcoff s (Or.inl hs))
    (fun τ ↦ by
      obtain ⟨s, hs0, hs1, he⟩ := hd' τ
      rw [he]
      exact hClow s hs0 hs1)
    (fun τ ↦ by
      obtain ⟨s, hs, he⟩ := hb' τ
      rw [he]
      exact hcoff s (Or.inr hs))
    hL hR
  obtain ⟨e, he⟩ := RiemannRochTop_homeomorph_pi1_map Ψ y₀
  apply e.injective
  rw [he, he]
  exact congrArg FundamentalGroup.fromPath
    (Quotient.sound (hE.symm.trans (hhom.trans hC')))

theorem hg3_loop_difference {X : Type*} [TopologicalSpace X] {a b : X}
    (A B C : Path a b) :
    FundamentalGroup.fromPath ⟦A.trans B.symm⟧ =
      (FundamentalGroup.fromPath ⟦B.trans C.symm⟧)⁻¹ *
        FundamentalGroup.fromPath ⟦A.trans C.symm⟧ := by
  rw [FundamentalGroup.inv_def, FundamentalGroup.mul_def]
  change FundamentalGroup.fromPath (.mk (A.trans B.symm)) =
    FundamentalGroup.fromPath
      ((Path.Homotopic.Quotient.mk (A.trans C.symm)).trans
        (Path.Homotopic.Quotient.mk (B.trans C.symm)).symm)
  apply congrArg FundamentalGroup.fromPath
  rw [← Path.Homotopic.Quotient.mk_symm, Path.trans_symm, Path.symm_symm]
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc (.mk C.symm) (.mk C) (.mk B.symm),
    show Path.Homotopic.Quotient.mk C.symm = (Path.Homotopic.Quotient.mk C).symm from rfl,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem hg3_cyclic_difference_product {G : Type*} [Group G] (h : Fin 13 → G) :
    (List.ofFn (fun i ↦ (h (finRotate 13 i))⁻¹ * h i)).reverse.prod = 1 := by
  change ((h 0)⁻¹ * h 12) * (((h 12)⁻¹ * h 11) * (((h 11)⁻¹ * h 10) * (((h 10)⁻¹ * h 9) * (((h 9)⁻¹ * h 8) * (((h 8)⁻¹ * h 7) * (((h 7)⁻¹ * h 6) * (((h 6)⁻¹ * h 5) * (((h 5)⁻¹ * h 4) * (((h 4)⁻¹ * h 3) * (((h 3)⁻¹ * h 2) * (((h 2)⁻¹ * h 1) * (((h 1)⁻¹ * h 0) * (1))))))))))))) = 1
  simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_one, inv_mul_cancel]

theorem hg3_ell_isLoop_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (y₀ y₁ : b6t_punctured t) (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (i : Fin 13) :
    FundamentalGroup.fromPath ⟦(F i).trans (F (finRotate 13 i)).symm⟧ = γ i := by
  have hfinite (j : Fin 12) :
      FundamentalGroup.fromPath
        ⟦(F j.castSucc).trans (F (finRotate 13 j.castSucc)).symm⟧ = γ j.castSucc := by
    obtain ⟨P, hP, hPc⟩ := hγ j.castSucc
    rw [← hPc]
    exact hg3_ell_finite t ht y₀ y₁ F hF j P hP
  induction i using Fin.lastCases with
  | cast j => exact hfinite j
  | last =>
    let δ (i : Fin 13) : FundamentalGroup (b6t_punctured t) y₀ :=
      FundamentalGroup.fromPath ⟦(F i).trans (F (finRotate 13 i)).symm⟧
    have hδ : (List.ofFn δ).reverse.prod = 1 := by
      have hh := hg3_cyclic_difference_product
        (fun i ↦ FundamentalGroup.fromPath ⟦(F i).trans (F 0).symm⟧)
      convert hh using 1
      congr 2
      apply congrArg List.ofFn
      funext i
      exact hg3_loop_difference (F i) (F (finRotate 13 i)) (F 0)
    have hγprod := mr_loops_product t ht y₀ γ hγ
    rw [mr_reverse_prod_last] at hδ hγprod
    have heq : (fun j : Fin 12 ↦ δ j.castSucc) = (fun j : Fin 12 ↦ γ j.castSucc) :=
      funext hfinite
    rw [heq] at hδ
    exact mul_right_cancel (hδ.trans hγprod.symm)

theorem hg3_lift_endpoint_aux {X U : Type*} [TopologicalSpace X] [TopologicalSpace U]
    {G : Type*} [Group G] [MulAction G U] {π : U → X} (hπ : IsQuotientCoveringMap π G)
    {x₀ : X} (u₀ : π ⁻¹' {x₀}) (c : Path x₀ x₀) (k : G)
    (hk : hπ.fundamentalGroupToMulOpposite u₀ (FundamentalGroup.fromPath ⟦c⟧) =
      MulOpposite.op k)
    (x : G) (Γ : C(unitInterval, U)) (hΓ : ∀ s, π (Γ s) = c s) (h0 : Γ 0 = x • (u₀ : U)) :
    Γ 1 = (x * k) • (u₀ : U) := by
  have hk' := hπ.fundamentalGroupToMulOpposite_apply_eq_iff.mp hk
  have hm := hπ.monodromy_toPermFiber
    (γ := (FundamentalGroup.fromPath ⟦c⟧).asHom) (e := u₀) (g := x)
  have he := hπ.isCoveringMap.monodromy_eq_apply_one
    (e := hπ.toPermFiber x₀ x u₀) (γ := c) (Γ := Γ) (funext hΓ) h0
  rw [← he]
  change (hπ.isCoveringMap.monodromy
    (FundamentalGroup.fromPath ⟦c⟧).asHom (hπ.toPermFiber x₀ x u₀) : U) = _
  rw [hm]
  change x • (hπ.isCoveringMap.monodromy
    (FundamentalGroup.fromPath ⟦c⟧).asHom u₀ : U) = _
  rw [← hk']
  exact (mul_smul x k (u₀ : U)).symm

theorem hg3_ell_endpoint_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    {G : Type*} [Group G] (g : Fin 13 → G)
    (U : Type*) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π G)
    (y₀ y₁ : b6t_punctured t) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (i : Fin 13) (x : G) (Γ : C(unitInterval, U))
    (hΓ : ∀ s, π (Γ s) = ((F i).trans (F (finRotate 13 i)).symm) s)
    (h0 : Γ 0 = x • (u₀ : U)) :
    Γ 1 = (x * g i) • (u₀ : U) := by
  apply hg3_lift_endpoint_aux hπ u₀ _ (g i) _ x Γ hΓ h0
  rw [hg3_ell_isLoop_aux t ht y₀ y₁ F hF γ hγ i]
  exact hroot i

theorem hg3_transport_retrace {X U : Type*} [TopologicalSpace X] [TopologicalSpace U]
    {π : U → X} (hπ : IsCoveringMap π) {a b : X} (P : Path a b)
    (u : π ⁻¹' {a}) :
    hπ.monodromy (.mk P.symm) (hπ.monodromy (.mk P) u) = u := by
  rw [← hπ.monodromy_trans_apply, ← Path.Homotopic.Quotient.mk_trans]
  have hh : Path.Homotopic.Quotient.mk (P.trans P.symm) =
      Path.Homotopic.Quotient.mk (Path.refl a) :=
    Quotient.sound ⟨(Path.Homotopy.reflTransSymm P).symm⟩
  rw [hh, Path.Homotopic.Quotient.mk_refl, hπ.monodromy_refl]
  rfl

theorem hg3_arc_endpoint_aux (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    {G : Type*} [Group G] (g : Fin 13 → G)
    (U : Type*) [TopologicalSpace U] [MulAction G U]
    (π : U → b6t_punctured t) (hπ : IsQuotientCoveringMap π G)
    (y₀ y₁ : b6t_punctured t) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured t) y₀) (hγ : ∀ i, mr_IsLoop t y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (g i))
    (F : Fin 13 → Path y₀ y₁)
    (hF : ∀ i (s : unitInterval), (F i s : OnePoint ℂ) = ((hg3_arc i s : ℂ) : OnePoint ℂ))
    (Δ : C(unitInterval, U)) (hΔ : ∀ s, π (Δ s) = F 0 s) (hΔ0 : Δ 0 = (u₀ : U))
    (i : Fin 13) (y : G) (Γ : C(unitInterval, U)) (hΓ : ∀ s, π (Γ s) = F i s)
    (h0 : Γ 0 = y • (u₀ : U)) :
    Γ 1 = (y * (hg_Q g i)⁻¹) • Δ 1 := by
  let T (j : Fin 13) : π ⁻¹' {y₁} := hπ.isCoveringMap.monodromy ⟦F j⟧ u₀
  have hstep (j : Fin 13) :
      (T j : U) = g j • (T (finRotate 13 j) : U) := by
    have hk := hπ.fundamentalGroupToMulOpposite_apply_eq_iff.mp (hroot j)
    rw [← hg3_ell_isLoop_aux t ht y₀ y₁ F hF γ hγ j] at hk
    change g j • (u₀ : U) =
      (hπ.isCoveringMap.monodromy ⟦(F j).trans (F (finRotate 13 j)).symm⟧ u₀ : U) at hk
    have hh : hπ.toPermFiber y₀ (g j) u₀ =
        hπ.isCoveringMap.monodromy ⟦(F (finRotate 13 j)).symm⟧ (T j) := by
      apply Subtype.ext
      change g j • (u₀ : U) =
        (hπ.isCoveringMap.monodromy
          ((Path.Homotopic.Quotient.mk (F j)).trans (.mk (F (finRotate 13 j)).symm)) u₀ : U) at hk
      rw [hπ.isCoveringMap.monodromy_trans_apply] at hk
      exact hk
    have hr := hg3_transport_retrace hπ.isCoveringMap (F (finRotate 13 j)) u₀
    have hc := hπ.monodromy_toPermFiber
      (γ := ⟦(F (finRotate 13 j)).symm⟧) (e := T (finRotate 13 j)) (g := g j)
    change (T j : U) = (hπ.toPermFiber y₁ (g j) (T (finRotate 13 j)) : U)
    apply congrArg Subtype.val
    apply (hπ.isCoveringMap.monodromy_bijective ⟦(F (finRotate 13 j)).symm⟧).injective
    exact hh.symm.trans (hc.trans (congrArg (hπ.toPermFiber y₀ (g j)) hr)).symm
  have hT : ∀ j : Fin 13, (T j : U) = (hg_Q g j)⁻¹ • (T 0 : U) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      rw [show hg_Q g 0 = 1 from hg_Q_zero g (by decide)]
      simp only [inv_one, one_smul]
    | succ j ih =>
      have hs := hstep j.castSucc
      have hj : finRotate 13 j.castSucc = j.succ := by
        apply Fin.ext
        rw [hg_finRotate_val]
        simp
        omega
      rw [hj, ih] at hs
      have hQ : hg_Q g j.succ = hg_Q g j.castSucc * g j.castSucc :=
        hg_Q_succ g j.castSucc (by simp; omega)
      rw [hQ, mul_inv_rev, mul_smul]
      exact (eq_inv_smul_iff).mpr hs.symm
  have hΔ1 : (T 0 : U) = Δ 1 :=
    hπ.isCoveringMap.monodromy_eq_apply_one (funext hΔ) hΔ0
  have he := hπ.isCoveringMap.monodromy_eq_apply_one
    (e := hπ.toPermFiber y₀ y u₀) (γ := F i) (Γ := Γ) (funext hΓ) h0
  rw [← he, hπ.monodromy_toPermFiber]
  change y • (T i : U) = _
  rw [hT i, hΔ1, mul_smul]

end HodgeLean.Foundations.Program
