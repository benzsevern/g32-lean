import HodgeLean.Foundations.Program.BraidBridgesThreeRoots
import HodgeLean.Foundations.Program.BraidBridgesThreeIsotopy

/-! # The moving configuration and the slot lassos at time zero

The certified lasso discs are pairwise disjoint, lie inside the outer circle and below the base
point, and the line from the base point to the top of each disc misses every other disc. Hence
the configuration path is injective with the base point adjoined, and each slot lasso misses the
configuration at time zero.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex Set
namespace HodgeLean.Foundations.Program

theorem b65x_disc_sep_rat : ∀ j k : Fin 12, j ≠ k →
    (b65b_radius j + b65b_radius k) ^ 2 <
      ((b65b_vertex0 j).1 - (b65b_vertex0 k).1) ^ 2 +
        ((b65b_vertex0 j).2 - (b65b_vertex0 k).2) ^ 2 := by
  intro j k h
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd rfl h
    | norm_num [b65b_radius, b65b_vertex0]

theorem b65x_cone_rat : ∀ j k : Fin 12, j ≠ k →
    (b65b_radius k) ^ 2 * (((b65b_vertex0 j).1 + 11/2) ^ 2 +
        ((b65b_vertex0 j).2 + b65b_radius j - 10) ^ 2) <
      (((b65b_vertex0 j).1 + 11/2) * ((b65b_vertex0 k).2 - 10) -
        ((b65b_vertex0 j).2 + b65b_radius j - 10) * ((b65b_vertex0 k).1 + 11/2)) ^ 2 := by
  intro j k h
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd rfl h
    | norm_num [b65b_radius, b65b_vertex0]

theorem b65x_outer_rat : ∀ j : Fin 12,
    ((b65b_vertex0 j).1 + 11/2) ^ 2 + (b65b_vertex0 j).2 ^ 2 < (10 - b65b_radius j) ^ 2 ∧
      (b65b_vertex0 j).2 + b65b_radius j < 10 ∧ 0 < b65b_radius j := by
  intro j
  fin_cases j <;> norm_num [b65b_radius, b65b_vertex0]

/-- The centre of the `j`-th lasso disc. -/
theorem b65x_track0 (j : Fin 12) :
    b65b_track 0 j = ((b65b_vertex0 j).1 : ℂ) + ((b65b_vertex0 j).2 : ℂ) * I := by
  simp [b65b_track]

theorem b65x_norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem b65x_disc_sep (j k : Fin 12) (h : j ≠ k) :
    (b65b_radius j : ℝ) + b65b_radius k < ‖b65b_track 0 j - b65b_track 0 k‖ := by
  have hq := b65x_disc_sep_rat j k h
  have hR := (Rat.cast_lt (K := ℝ)).mpr hq
  push_cast at hR
  have hpos : (0 : ℝ) ≤ b65b_radius j + b65b_radius k := by
    have := (b65x_outer_rat j).2.2; have := (b65x_outer_rat k).2.2
    have : (0 : ℚ) ≤ b65b_radius j + b65b_radius k := by linarith
    exact_mod_cast this
  have hn : ‖b65b_track 0 j - b65b_track 0 k‖ ^ 2 =
      (((b65b_vertex0 j).1 : ℝ) - (b65b_vertex0 k).1) ^ 2 +
        (((b65b_vertex0 j).2 : ℝ) - (b65b_vertex0 k).2) ^ 2 := by
    rw [b65x_norm_sq, b65x_track0, b65x_track0]; simp
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [hn]; exact hR

theorem b65x_cross_le (a b : ℂ) : |a.re * b.im - a.im * b.re| ≤ ‖a‖ * ‖b‖ := by
  rw [abs_le]
  have h1 : (a.re * b.im - a.im * b.re) ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [mul_pow, b65x_norm_sq, b65x_norm_sq]
    nlinarith [sq_nonneg (a.re * b.re + a.im * b.im)]
  have h2 : 0 ≤ ‖a‖ * ‖b‖ := by positivity
  constructor <;> nlinarith [sq_nonneg (a.re * b.im - a.im * b.re + ‖a‖ * ‖b‖),
    sq_nonneg (a.re * b.im - a.im * b.re - ‖a‖ * ‖b‖)]

/-- Points of a disc are not on the segment from the base point to the top of another disc. -/
theorem b65x_segment_avoid (j k : Fin 12) (h : j ≠ k) (lam : ℝ) (q : ℂ)
    (hq : ‖q - b65b_track 0 k‖ < b65b_radius k) :
    mr_basePoint + (lam : ℂ) * (b65b_track 0 j + I * (b65b_radius j : ℝ) - mr_basePoint) ≠ q := by
  intro he
  set u : ℂ := b65b_track 0 j + I * (b65b_radius j : ℝ) - mr_basePoint with hu
  set w : ℂ := b65b_track 0 k - mr_basePoint with hw
  have hcone := (Rat.cast_lt (K := ℝ)).mpr (b65x_cone_rat j k h)
  push_cast at hcone
  have hure : u.re = (b65b_vertex0 j).1 + 11/2 := by
    simp [hu, b65x_track0, mr_basePoint, mr_centre]; ring
  have huim : u.im = (b65b_vertex0 j).2 + b65b_radius j - 10 := by
    simp [hu, b65x_track0, mr_basePoint, mr_centre]
  have hwre : w.re = (b65b_vertex0 k).1 + 11/2 := by
    simp [hw, b65x_track0, mr_basePoint, mr_centre]; ring
  have hwim : w.im = (b65b_vertex0 k).2 - 10 := by
    simp [hw, b65x_track0, mr_basePoint, mr_centre]
  have hcone' : (b65b_radius k : ℝ) ^ 2 * ‖u‖ ^ 2 < (u.re * w.im - u.im * w.re) ^ 2 := by
    rw [b65x_norm_sq, hure, huim, hwre, hwim]; exact hcone
  -- the cross product with the direction is unchanged along the line
  have hd : q - b65b_track 0 k = (lam : ℂ) * u - w := by
    rw [← he, hu, hw]; ring
  have hcr : u.re * (q - b65b_track 0 k).im - u.im * (q - b65b_track 0 k).re =
      -(u.re * w.im - u.im * w.re) := by
    rw [hd]; simp; ring
  have hb := b65x_cross_le u (q - b65b_track 0 k)
  rw [hcr, abs_neg] at hb
  have hX : (u.re * w.im - u.im * w.re) ^ 2 ≤ (‖u‖ * ‖q - b65b_track 0 k‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hY : (‖u‖ * ‖q - b65b_track 0 k‖) ^ 2 ≤ (‖u‖ * (b65b_radius k : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hq.le (norm_nonneg _)
  nlinarith

/-- The index of the disc of a column lasso. -/
def b65x_colDisc (c : Fin 13) (hc : c.val ≠ 0) : Fin 12 := ⟨13 - c.val - 1, by omega⟩

/-- A column lasso is on the segment to the top of its disc or on the boundary circle. -/
theorem b65x_lasso_cases (c : Fin 13) (hc : c.val ≠ 0) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∃ lam ∈ Icc (0 : ℝ) 1, b65b_lasso c s = mr_basePoint + (lam : ℂ) *
      (b65b_track 0 (b65x_colDisc c hc) + I * (b65b_radius (b65x_colDisc c hc) : ℝ) -
        mr_basePoint)) ∨
    ‖b65b_lasso c s - b65b_track 0 (b65x_colDisc c hc)‖ = b65b_radius (b65x_colDisc c hc) := by
  have hr : (0 : ℝ) < b65b_radius (b65x_colDisc c hc) := by
    exact_mod_cast (b65x_outer_rat _).2.2
  unfold b65b_lasso
  rw [dite_eq_right hc]
  split_ifs with h1 h2
  · left
    refine ⟨3 * s, ⟨by linarith [hs.1], by linarith⟩, ?_⟩
    simp [b65x_colDisc, Complex.ofReal_ratCast]
  · right
    change ‖b65b_track 0 (b65x_colDisc c hc) + I * ((b65b_radius (b65x_colDisc c hc) : ℚ) : ℂ) *
      cexp (2 * (Real.pi : ℂ) * I * (3 * (s : ℂ) - 1)) - b65b_track 0 (b65x_colDisc c hc)‖ = _
    rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * I * (3 * (s : ℂ) - 1)).re = 0 := by
      simp
    rw [this, Real.exp_zero, mul_one]
    have hr' : (0 : ℚ) ≤ b65b_radius (b65x_colDisc c hc) := (b65x_outer_rat _).2.2.le
    simpa [b65x_colDisc] using hr'
  · left
    refine ⟨3 - 3 * s, ⟨by linarith [hs.2], by linarith⟩, ?_⟩
    simp [b65x_colDisc, Complex.ofReal_ratCast]

/-- A point strictly inside its disc is not on the segment to the top of that disc. -/
theorem b65x_segment_own (j : Fin 12) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) (q : ℂ)
    (hq : ‖q - b65b_track 0 j‖ < b65b_radius j) :
    mr_basePoint + (lam : ℂ) * (b65b_track 0 j + I * (b65b_radius j : ℝ) - mr_basePoint) ≠ q := by
  intro he
  have hb := (b65x_outer_rat j).2.1
  have hb' : ((b65b_vertex0 j).2 : ℝ) + b65b_radius j < 10 := by exact_mod_cast hb
  have him : (q - b65b_track 0 j).im = 10 + lam * ((b65b_vertex0 j).2 + b65b_radius j - 10) -
      (b65b_vertex0 j).2 := by
    rw [← he]; simp [b65x_track0, mr_basePoint, mr_centre]
  have h1 : (b65b_radius j : ℝ) ≤ (q - b65b_track 0 j).im := by
    rw [him]; nlinarith [hlam.1, hlam.2]
  have h2 := Complex.abs_im_le_norm (q - b65b_track 0 j)
  have h3 := le_abs_self (q - b65b_track 0 j).im
  linarith

/-- Each column lasso misses every point lying in a lasso disc. -/
theorem b65x_lasso_avoid (c : Fin 13) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (k : Fin 12) (q : ℂ)
    (hq : ‖q - b65b_track 0 k‖ < b65b_radius k) : b65b_lasso c s ≠ q := by
  by_cases hc : c.val = 0
  · have hc0 : c = 0 := Fin.ext hc
    subst hc0
    intro he
    have hout := (b65x_outer_rat k).1
    have hout' := (Rat.cast_lt (K := ℝ)).mpr hout
    push_cast at hout'
    have hc10 : ‖b65b_track 0 k + 11/2‖ < 10 - b65b_radius k := by
      have hr : (b65b_radius k : ℝ) < 10 := by
        have := (b65x_outer_rat k).2
        have h' : (b65b_radius k : ℚ) < 10 := by nlinarith [this.1, this.2]
        exact_mod_cast h'
      apply lt_of_pow_lt_pow_left₀ 2 (by linarith)
      rw [b65x_norm_sq, b65x_track0]; simpa using hout'
    have hw : ‖b65b_lasso 0 s + 11/2‖ = 10 := by
      simp only [b65b_lasso, dite_eq_left (show (0 : Fin 13).val = 0 from rfl), mr_outer, mr_centre]
      rw [show -11 / 2 + 10 * I * cexp (-(2 * Real.pi * I * (s : ℂ))) + 11 / 2 =
        10 * I * cexp (-(2 * Real.pi * I * (s : ℂ))) by ring]
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp]
      simp
    rw [he] at hw
    have := norm_add_le (q - b65b_track 0 k) (b65b_track 0 k + 11/2)
    rw [show q - b65b_track 0 k + (b65b_track 0 k + 11/2) = q + 11/2 by ring] at this
    linarith
  · set j := b65x_colDisc c hc
    rcases b65x_lasso_cases c hc s hs with ⟨lam, hlam, he⟩ | hcirc
    · rw [he]
      by_cases hjk : j = k
      · rw [← hjk] at hq; exact b65x_segment_own j lam hlam q hq
      · exact b65x_segment_avoid j k hjk lam q hq
    · intro he
      rw [he] at hcirc
      by_cases hjk : j = k
      · rw [← hjk] at hq; linarith
      · have hsep := b65x_disc_sep j k hjk
        have := norm_sub_le (b65b_track 0 j - q) (b65b_track 0 k - q)
        rw [show b65b_track 0 j - q - (b65b_track 0 k - q) = b65b_track 0 j - b65b_track 0 k by
          ring, norm_sub_rev (b65b_track 0 j) q, norm_sub_rev (b65b_track 0 k) q] at this
        linarith

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
/-- Up to time one half each point of the configuration stays in its open lasso disc. -/
theorem b65x_config_disc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) (j : Fin 12) :
    ‖b65b_configuration p t j - b65b_track 0 j‖ < b65b_radius j := by
  have hN := b65x_witness_disc p hp j
  rw [b65b_configuration, ite_eq_left ht.2]
  have he : (1 - 2 * (t : ℂ)) * b65s_normalize (p 10) (p 11) (p j) + 2 * (t : ℂ) * b65b_track 0 j -
      b65b_track 0 j = ((1 - 2 * t : ℝ) : ℂ) *
        (b65s_normalize (p 10) (p 11) (p j) - b65b_track 0 j) := by push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  have h0 := norm_nonneg (b65s_normalize (p 10) (p 11) (p j) - b65b_track 0 j)
  nlinarith [ht.1]

theorem b65x_configuration_continuous (p : Fin 12 → ℂ) :
    Continuous fun t : ℝ ↦ b65b_configuration p t := by
  apply continuous_pi
  intro j
  unfold b65b_configuration
  refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
  · unfold b65b_track; fun_prop
  · intro t ht
    rw [ht]
    simp [b65b_track]

include hp in
theorem b65x_config_injective (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective (b65b_configuration p t) ∧
      ∀ j, b65b_configuration p t j ≠ mr_basePoint := by
  by_cases h : t ≤ 1/2
  · have hd := fun j ↦ b65x_config_disc p hp t ⟨ht.1, h⟩ j
    refine ⟨fun i j hij ↦ ?_, fun j hj ↦ ?_⟩
    · by_contra hne
      have hsep := b65x_disc_sep i j hne
      have h1 := hd i
      have h2 := hd j
      rw [hij] at h1
      have := norm_sub_le (b65b_track 0 i - b65b_configuration p t j)
        (b65b_track 0 j - b65b_configuration p t j)
      rw [show b65b_track 0 i - b65b_configuration p t j -
          (b65b_track 0 j - b65b_configuration p t j) = b65b_track 0 i - b65b_track 0 j by
        ring] at this
      have e1 := norm_sub_rev (b65b_track 0 i) (b65b_configuration p t j)
      have e2 := norm_sub_rev (b65b_track 0 j) (b65b_configuration p t j)
      linarith
    · have h1 := hd j
      rw [hj] at h1
      have hb := (b65x_outer_rat j).2.1
      have hb' : ((b65b_vertex0 j).2 : ℝ) + b65b_radius j < 10 := by exact_mod_cast hb
      have him : (mr_basePoint - b65b_track 0 j).im = 10 - (b65b_vertex0 j).2 := by
        simp [b65x_track0, mr_basePoint, mr_centre]
      have h2 : 10 - ((b65b_vertex0 j).2 : ℝ) ≤ ‖mr_basePoint - b65b_track 0 j‖ := by
        have := Complex.abs_im_le_norm (mr_basePoint - b65b_track 0 j)
        rw [him] at this
        exact (le_abs_self _).trans this
      linarith
  · push Not at h
    have hconf : b65b_configuration p t = b65b_track (2 * t - 1) := by
      funext j; rw [b65b_configuration, ite_eq_right (not_le.mpr h)]
    have hu : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
    rw [hconf]
    refine ⟨b65b_path_geometry.1 _ hu, fun j hj ↦ ?_⟩
    have h1 := b65b_path_geometry.2.1 _ hu j
    rw [hj] at h1
    simp [mr_basePoint, mr_centre] at h1

/-- The configuration with the base point adjoined as a stationary last point. -/
def b65x_withBase (p : Fin 12 → ℂ) (t : ℝ) (j : Fin 13) : ℂ :=
  if h : j.val < 12 then b65b_configuration p t ⟨j.val, h⟩ else mr_basePoint

theorem b65x_withBase_continuous (p : Fin 12 → ℂ) : Continuous (b65x_withBase p) := by
  apply continuous_pi
  intro j
  unfold b65x_withBase
  by_cases h : j.val < 12
  · simp only [dite_eq_left h]
    exact (continuous_apply _).comp (b65x_configuration_continuous p)
  · simp only [dite_eq_right h]
    exact continuous_const

theorem b65x_withBase_cast (p : Fin 12 → ℂ) (t : ℝ) (j : Fin 12) :
    b65x_withBase p t j.castSucc = b65b_configuration p t j := by
  simp [b65x_withBase]

theorem b65x_withBase_last (p : Fin 12 → ℂ) (t : ℝ) :
    b65x_withBase p t (Fin.last 12) = mr_basePoint := by
  simp [b65x_withBase]

include hp in
theorem b65x_withBase_injective (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective (b65x_withBase p t) := by
  obtain ⟨hinj, hbase⟩ := b65x_config_injective p hp t ht
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
      rw [b65x_withBase_last, b65x_withBase_cast] at hij
      exact absurd hij.symm (hbase j)
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [b65x_withBase_last, b65x_withBase_cast] at hij
      exact absurd hij (hbase i)
    | cast j =>
      rw [b65x_withBase_cast, b65x_withBase_cast] at hij
      rw [hinj hij]

include hp in
/-- The moving based lasso family obtained by pushing the slot lassos along the isotopy. -/
theorem b65x_moving_family :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) := by
  obtain ⟨Φ, E, hE, hbij, h0, htr⟩ := b65x_isotopy_sphere (b65x_withBase p)
    (b65x_withBase_continuous p) (b65x_withBase_injective p hp)
  have hlc : ∀ c : Fin 13, Continuous fun s : unitInterval ↦ b65b_lasso c s :=
    fun c ↦ (b65x_lasso_continuous_plane c).comp continuous_subtype_val
  let K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ) := fun i ↦
    ⟨fun q ↦ (E (q.1, (b65b_lasso (b65x_slot i) q.2 : OnePoint ℂ))).2, by
      refine continuous_snd.comp (E.continuous.comp (continuous_fst.prodMk ?_))
      exact OnePoint.continuous_coe.comp ((hlc _).comp continuous_snd)⟩
  have hK : ∀ i (t s : unitInterval),
      K i (t, s) = ((Φ t (b65b_lasso (b65x_slot i) s) : ℂ) : OnePoint ℂ) := by
    intro i t s
    change (E (t, _)).2 = _
    rw [hE]; rfl
  have hB : ∀ t : unitInterval, Φ t mr_basePoint = mr_basePoint := by
    intro t
    have h := htr t t.2 (Fin.last 12)
    rwa [b65x_withBase_last, b65x_withBase_last] at h
  refine ⟨K, fun i s ↦ ?_, fun i t ↦ ⟨?_, ?_⟩, fun i t s ↦ ⟨?_, fun j ↦ ?_⟩⟩
  · rw [hK]
    simp only [Set.Icc.coe_zero, h0]
  · rw [hK, show ((0 : unitInterval) : ℝ) = 0 from rfl, b65x_lasso_zero, hB]
  · rw [hK, show ((1 : unitInterval) : ℝ) = 1 from rfl, b65x_lasso_one, hB]
  · rw [hK]; exact OnePoint.coe_ne_infty _
  · rw [hK]
    intro he
    have he' := OnePoint.coe_injective he
    have h1 := htr t t.2 j.castSucc
    rw [b65x_withBase_cast, b65x_withBase_cast, ← he'] at h1
    have h2 := (hbij t).1 h1
    have hd := b65x_config_disc p hp 0 ⟨le_rfl, by norm_num⟩ j
    exact b65x_lasso_avoid _ s ⟨s.2.1, s.2.2⟩ j _ hd h2.symm

end Witness

end HodgeLean.Foundations.Program
