import HodgeLean.Foundations.Program.BraidBridgesThreeShapes
import HodgeLean.Foundations.Program.BraidBridgesThreePath

/-! # Unblocked radial lassos along the certified path and along an auxiliary path

Along the certified configuration path no point lies on the segment from the base point to any
point other than p10: before time one half the points are in different cones, afterwards
collinearity happens only at the two certified events, where p10 is the farther point. Along an
auxiliary path that moves the disc centres radially to the real axis and then along the axis to
the marks, no point is ever blocked.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex Set
namespace HodgeLean.Foundations.Program

theorem b65x_cross_star (z w : ℂ) : (z * (starRingEnd ℂ) w).im = -b65x_cross z w := by
  simp [b65x_cross, Complex.mul_im]; ring

theorem b65x_on_seg {w v : ℂ} {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (he : mr_basePoint + (μ : ℂ) * (w - mr_basePoint) = v) :
    b65x_cross (w - mr_basePoint) (v - mr_basePoint) = 0 ∧
      ‖v - mr_basePoint‖ ≤ ‖w - mr_basePoint‖ := by
  refine ⟨by rw [← he]; exact b65x_cross_seg w μ (Complex.ofReal_im μ), ?_⟩
  rw [← he, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hμ.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hμ.2

theorem b65x_marks_cross (a b : Fin 12) (h : a ≠ b) :
    b65x_cross (mr_marks a - mr_basePoint) (mr_marks b - mr_basePoint) ≠ 0 := by
  have hre : (mr_marks a).re ≠ (mr_marks b).re := by
    intro he
    have := b65x_marks_sep a b h
    have h2 : (mr_marks a - mr_marks b) = 0 := by
      apply Complex.ext
      · simp [he]
      · simp [b65x_marks_im]
    rw [h2, norm_zero] at this
    norm_num at this
  simp only [b65x_cross, Complex.sub_re, Complex.sub_im, b65x_marks_im]
  simp only [mr_basePoint, mr_centre]
  simp
  intro h'
  apply hre
  linarith

theorem b65x_event_far_rat :
    ((1 - (63109263/2063109263 : ℚ)) * (b65b_vertex0 8).1 +
        (63109263/2063109263 : ℚ) * (b65b_vertex1 8).1 + 11/2) ^ 2 +
      ((1 - (63109263/2063109263 : ℚ)) * (b65b_vertex0 8).2 +
        (63109263/2063109263 : ℚ) * (b65b_vertex1 8).2 - 10) ^ 2 < (11/2) ^ 2 + 10 ^ 2 ∧
    ((1 - (48671253/298671253 : ℚ)) * (b65b_vertex0 9).1 +
        (48671253/298671253 : ℚ) * (b65b_vertex1 9).1 + 11/2) ^ 2 +
      ((1 - (48671253/298671253 : ℚ)) * (b65b_vertex0 9).2 +
        (48671253/298671253 : ℚ) * (b65b_vertex1 9).2 - 10) ^ 2 < (11/2) ^ 2 + 10 ^ 2 := by
  norm_num [b65b_vertex0, b65b_vertex1]

theorem b65x_track_norm_sq (u : ℝ) (j : Fin 12) :
    ‖b65b_track u j - mr_basePoint‖ ^ 2 =
      ((1 - u) * (b65b_vertex0 j).1 + u * (b65b_vertex1 j).1 + 11/2) ^ 2 +
        ((1 - u) * (b65b_vertex0 j).2 + u * (b65b_vertex1 j).2 - 10) ^ 2 := by
  rw [b65x_norm_sq]
  simp [b65b_track, mr_basePoint, mr_centre]
  ring

theorem b65x_track10 (u : ℝ) : b65b_track u 10 = 0 := by
  simp [b65b_track, b65b_vertex0, b65b_vertex1]

/-- At the two certified events p10 is farther from the base point than the nearer point. -/
theorem b65x_event_far :
    ‖b65b_track (63109263/2063109263 : ℝ) 8 - mr_basePoint‖ <
        ‖b65b_track (63109263/2063109263 : ℝ) 10 - mr_basePoint‖ ∧
      ‖b65b_track (48671253/298671253 : ℝ) 9 - mr_basePoint‖ <
        ‖b65b_track (48671253/298671253 : ℝ) 10 - mr_basePoint‖ := by
  have h := b65x_event_far_rat
  have h1 := (Rat.cast_lt (K := ℝ)).mpr h.1
  have h2 := (Rat.cast_lt (K := ℝ)).mpr h.2
  push_cast at h1 h2
  have h10 : ‖(0 : ℂ) - mr_basePoint‖ ^ 2 = (11/2) ^ 2 + 10 ^ 2 := by
    rw [b65x_norm_sq]; simp [mr_basePoint, mr_centre]; norm_num
  constructor
  · apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
    rw [b65x_track_norm_sq, b65x_track10, h10]; exact h1
  · apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
    rw [b65x_track_norm_sq, b65x_track10, h10]; exact h2

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
/-- Along the certified path only p10 can be blocked. -/
theorem b65x_main_unblocked (a : Fin 12) (ha : a ≠ 10) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (b : Fin 12) (hba : b ≠ a) (μ : ℝ) (hμ : μ ∈ Icc (0 : ℝ) 1) :
    mr_basePoint + (μ : ℂ) * (b65b_configuration p t a - mr_basePoint) ≠
      b65b_configuration p t b := by
  intro he
  obtain ⟨hcr, hle⟩ := b65x_on_seg hμ he
  by_cases h : t ≤ 1/2
  · exact b65x_cone_robust a b (Ne.symm hba) _ _ (b65x_config_disc p hp t ⟨ht.1, h⟩ a).le
      (b65x_config_disc p hp t ⟨ht.1, h⟩ b).le hcr
  push Not at h
  have hconf : b65b_configuration p t = b65b_track (2 * t - 1) := by
    funext j; rw [b65b_configuration, ite_eq_right (not_le.mpr h)]
  rw [hconf] at hcr hle
  set u := 2 * t - 1
  by_cases hu : u < 1
  · have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨by simp only [u]; linarith, hu⟩
    have hgeo := b65b_path_geometry.2.2 u huI
    have hBdef : mr_basePoint = -11/2 + 10 * I := by simp [mr_basePoint, mr_centre]
    have key : ∀ i j, ((b65b_track u i - (-11/2 + 10 * I)) *
        star (b65b_track u j - (-11/2 + 10 * I))).im =
          -b65x_cross (b65b_track u i - mr_basePoint) (b65b_track u j - mr_basePoint) := by
      intro i j; rw [← hBdef]; exact b65x_cross_star _ _
    have hswap : b65x_cross (b65b_track u b - mr_basePoint) (b65b_track u a - mr_basePoint) = 0 := by
      have : b65x_cross (b65b_track u b - mr_basePoint) (b65b_track u a - mr_basePoint) =
          -b65x_cross (b65b_track u a - mr_basePoint) (b65b_track u b - mr_basePoint) := by
        simp only [b65x_cross]; ring
      rw [this, hcr, neg_zero]
    rcases lt_or_gt_of_ne hba with hlt | hlt
    · have hev := (hgeo b a hlt).mp (by rw [key, hswap, neg_zero])
      rcases hev with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> exact ha rfl
    · have hev := (hgeo a b hlt).mp (by rw [key, hcr, neg_zero])
      rcases hev with ⟨rfl, rfl, hτ⟩ | ⟨rfl, rfl, hτ⟩
      · have := b65x_event_far.1
        rw [← hτ] at this
        linarith
      · have := b65x_event_far.2
        rw [← hτ] at this
        linarith
  · have hu1 : u = 1 := le_antisymm (by simp only [u]; linarith [ht.2]) (not_lt.mp hu)
    have hm : ∀ j, b65b_track u j = mr_marks j := by
      intro j
      rw [← b65x_configuration_one p j, b65b_configuration, ite_eq_right (by norm_num), hu1]
      norm_num
    rw [hm, hm] at hcr
    exact b65x_marks_cross a b (Ne.symm hba) hcr

end Witness

/-- Final mark of each point along the auxiliary path. -/
def b65x_auxMark : Fin 12 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 8, 11]

/-- Radial projection of a disc centre from the base point to the real axis. -/
def b65x_proj (k : Fin 12) : ℚ :=
  -11/2 + 10 * ((b65b_vertex0 k).1 + 11/2) / (10 - (b65b_vertex0 k).2)

/-- The auxiliary path: the first half of the certified path, radial projection of the centres to
the real axis, and motion along the axis to the marks. -/
def b65x_aux (p : Fin 12 → ℂ) (τ : ℝ) (k : Fin 12) : ℂ :=
  if τ ≤ 1/3 then b65b_configuration p (3 * τ / 2) k
  else if τ ≤ 2/3 then b65b_track 0 k + ((3 * τ - 1 : ℝ) : ℂ) * (((b65x_proj k : ℝ) : ℂ) - b65b_track 0 k)
  else ((b65x_proj k : ℝ) : ℂ) + ((3 * τ - 2 : ℝ) : ℂ) *
    (mr_marks (b65x_auxMark k) - ((b65x_proj k : ℝ) : ℂ))

theorem b65x_aux_continuous (p : Fin 12 → ℂ) : Continuous (b65x_aux p) := by
  apply continuous_pi
  intro k
  unfold b65x_aux
  refine Continuous.if_le ?_ (Continuous.if_le (by fun_prop) (by fun_prop) continuous_id
    continuous_const ?_) continuous_id continuous_const ?_
  · exact (continuous_apply k).comp ((b65x_configuration_continuous p).comp (by fun_prop))
  · intro τ hτ; rw [hτ]; push_cast; ring
  · intro τ hτ
    rw [hτ, ite_eq_left (by norm_num)]
    rw [show 3 * (1/3 : ℝ) / 2 = 1/2 by norm_num, b65b_configuration, ite_eq_left le_rfl]
    push_cast; ring

theorem b65x_aux_zero (p : Fin 12 → ℂ) : b65x_aux p 0 = b65b_configuration p 0 := by
  funext k; simp [b65x_aux]

theorem b65x_aux_one (p : Fin 12 → ℂ) (k : Fin 12) :
    b65x_aux p 1 k = mr_marks (b65x_auxMark k) := by
  simp only [b65x_aux]
  rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
  push_cast; ring

theorem b65x_proj_rat : ∀ k : Fin 12, 0 < 10 - (b65b_vertex0 k).2 ∧
    (b65x_proj k + 11/2) ^ 2 < 10 ^ 2 := by
  intro k; fin_cases k <;> norm_num [b65x_proj, b65b_vertex0]

/-- Real parts of the auxiliary final marks. -/
def b65x_auxMarkRe : Fin 12 → ℚ := ![-12, -11, -10, -9, -8, -7, -6, -5, -3, 0, -4, 1]

theorem b65x_auxMarkRe_eq (k : Fin 12) :
    (mr_marks (b65x_auxMark k)).re = (b65x_auxMarkRe k : ℝ) := by
  fin_cases k <;> norm_num [b65x_auxMark, b65x_auxMarkRe, mr_marks, mr_base, Fin.append,
    Fin.addCases]

/-- The points in increasing order of projection. -/
def b65x_sortPerm : Fin 12 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 8, 9, 11]
def b65x_sortInv : Fin 12 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 8, 11]

theorem b65x_sort_inv (a : Fin 12) : b65x_sortPerm (b65x_sortInv a) = a := by
  fin_cases a <;> rfl

theorem b65x_proj_sorted : StrictMono fun i ↦ b65x_proj (b65x_sortPerm i) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> norm_num [b65x_proj, b65b_vertex0, b65x_sortPerm]

theorem b65x_mark_sorted : StrictMono fun i ↦ b65x_auxMarkRe (b65x_sortPerm i) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> norm_num [b65x_auxMarkRe, b65x_sortPerm]

theorem b65x_proj_order_rat (a b : Fin 12) (h : a ≠ b) :
    (b65x_proj a < b65x_proj b ∧ b65x_auxMarkRe a < b65x_auxMarkRe b) ∨
    (b65x_proj b < b65x_proj a ∧ b65x_auxMarkRe b < b65x_auxMarkRe a) := by
  have hij : b65x_sortInv a ≠ b65x_sortInv b := by
    intro he; apply h; rw [← b65x_sort_inv a, ← b65x_sort_inv b, he]
  have ea := b65x_sort_inv a
  have eb := b65x_sort_inv b
  rcases lt_or_gt_of_ne hij with hl | hl
  · left
    have h1 := b65x_proj_sorted hl
    have h2 := b65x_mark_sorted hl
    simp only [ea, eb] at h1 h2
    exact ⟨h1, h2⟩
  · right
    have h1 := b65x_proj_sorted hl
    have h2 := b65x_mark_sorted hl
    simp only [ea, eb] at h1 h2
    exact ⟨h1, h2⟩

/-- The projection lies on the ray from the base point through the centre. -/
theorem b65x_proj_ray (k : Fin 12) :
    ((b65x_proj k : ℝ) : ℂ) - mr_basePoint =
      ((10 / (10 - (b65b_vertex0 k).2) : ℚ) : ℝ) * (b65b_track 0 k - mr_basePoint) := by
  have hpos := (b65x_proj_rat k).1
  set v1 : ℝ := ((b65b_vertex0 k).1 : ℝ)
  set v2 : ℝ := ((b65b_vertex0 k).2 : ℝ)
  have hne : (10 : ℝ) - v2 ≠ 0 := by
    have : (0 : ℝ) < 10 - v2 := by simp only [v2]; exact_mod_cast hpos
    exact this.ne'
  have e1 : ((b65x_proj k : ℚ) : ℝ) = -11/2 + 10 * (v1 + 11/2) / (10 - v2) := by
    simp only [b65x_proj, v1, v2]; push_cast; ring
  have e2 : (((10 / (10 - (b65b_vertex0 k).2) : ℚ) : ℝ)) = 10 / (10 - v2) := by
    simp only [v2]; push_cast; ring
  have hre : (b65b_track 0 k - mr_basePoint).re = v1 + 11/2 := by
    simp [b65x_track0, mr_basePoint, mr_centre, v1]; ring
  have him : (b65b_track 0 k - mr_basePoint).im = v2 - 10 := by
    simp [b65x_track0, mr_basePoint, mr_centre, v2]
  have hBre : mr_basePoint.re = -11/2 := by simp [mr_basePoint, mr_centre]
  have hBim : mr_basePoint.im = 10 := by simp [mr_basePoint, mr_centre]
  rw [e1, e2]
  apply Complex.ext
  · rw [Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, hBre]
    field_simp
    ring
  · rw [Complex.sub_im, Complex.ofReal_im, Complex.im_ofReal_mul, him, hBim]
    field_simp
    ring

theorem b65x_cross_smul (f g : ℝ) (z w : ℂ) :
    b65x_cross ((f : ℂ) * z) ((g : ℂ) * w) = f * g * b65x_cross z w := by
  simp [b65x_cross]; ring

theorem b65x_centre_disc (k : Fin 12) : ‖b65b_track 0 k - b65b_track 0 k‖ ≤ b65b_radius k := by
  rw [sub_self, norm_zero]; exact_mod_cast (b65x_outer_rat k).2.2.le

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

/-- In the second phase each point is a positive multiple of its centre direction. -/
theorem b65x_aux_phase2 (τ : ℝ) (h1 : ¬ τ ≤ 1/3) (h2 : τ ≤ 2/3) (k : Fin 12) :
    ∃ f : ℝ, 0 < f ∧ b65x_aux p τ k - mr_basePoint = (f : ℂ) * (b65b_track 0 k - mr_basePoint) := by
  have hΛ : (0 : ℝ) < ((10 / (10 - (b65b_vertex0 k).2) : ℚ) : ℝ) := by
    have := (b65x_proj_rat k).1
    have : (0 : ℚ) < 10 / (10 - (b65b_vertex0 k).2) := by positivity
    exact_mod_cast this
  set Λ : ℝ := ((10 / (10 - (b65b_vertex0 k).2) : ℚ) : ℝ)
  refine ⟨1 + (3 * τ - 1) * (Λ - 1), ?_, ?_⟩
  · push Not at h1
    have hl0 : 0 ≤ 3 * τ - 1 := by linarith
    have hl1 : 3 * τ - 1 ≤ 1 := by linarith
    nlinarith
  · simp only [b65x_aux, ite_eq_right h1, ite_eq_left h2]
    have hr := b65x_proj_ray k
    have : ((b65x_proj k : ℝ) : ℂ) = mr_basePoint + (Λ : ℂ) * (b65b_track 0 k - mr_basePoint) := by
      rw [← hr]; ring
    rw [this]; push_cast; ring

include hp in
theorem b65x_aux_unblocked (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) (a b : Fin 12) (hba : b ≠ a)
    (μ : ℝ) (hμ : μ ∈ Icc (0 : ℝ) 1) :
    mr_basePoint + (μ : ℂ) * (b65x_aux p τ a - mr_basePoint) ≠ b65x_aux p τ b := by
  intro he
  obtain ⟨hcr, -⟩ := b65x_on_seg hμ he
  by_cases h1 : τ ≤ 1/3
  · have ht : 3 * τ / 2 ∈ Icc (0 : ℝ) (1/2) := ⟨by linarith [hτ.1], by linarith⟩
    simp only [b65x_aux, ite_eq_left h1] at hcr
    exact b65x_cone_robust a b (Ne.symm hba) _ _ (b65x_config_disc p hp _ ht a).le
      (b65x_config_disc p hp _ ht b).le hcr
  by_cases h2 : τ ≤ 2/3
  · obtain ⟨fa, hfa, ea⟩ := b65x_aux_phase2 p τ h1 h2 a
    obtain ⟨fb, hfb, eb⟩ := b65x_aux_phase2 p τ h1 h2 b
    rw [ea, eb, b65x_cross_smul] at hcr
    have hc := b65x_cone_robust a b (Ne.symm hba) _ _ (b65x_centre_disc a) (b65x_centre_disc b)
    have : fa * fb ≠ 0 := by positivity
    exact hc ((mul_eq_zero.mp hcr).resolve_left this)
  · have hval : ∀ k, b65x_aux p τ k = (((b65x_proj k : ℝ) + (3 * τ - 2) *
        ((mr_marks (b65x_auxMark k)).re - b65x_proj k) : ℝ) : ℂ) := by
      intro k
      simp only [b65x_aux, ite_eq_right h1, ite_eq_right h2]
      apply Complex.ext <;> simp [b65x_marks_im]
    rw [hval, hval] at hcr
    simp only [b65x_cross, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im] at hcr
    simp only [mr_basePoint, mr_centre] at hcr
    simp at hcr
    push Not at h2
    have hl0 : 0 ≤ 3 * τ - 2 := by linarith
    have hl1 : 3 * τ - 2 ≤ 1 := by linarith [hτ.2]
    rw [b65x_auxMarkRe_eq, b65x_auxMarkRe_eq] at hcr
    rcases b65x_proj_order_rat a b (Ne.symm hba) with ⟨ho1, ho2⟩ | ⟨ho1, ho2⟩
    · have ho1' : (b65x_proj a : ℝ) < b65x_proj b := by exact_mod_cast ho1
      have ho2' : (b65x_auxMarkRe a : ℝ) < b65x_auxMarkRe b := by exact_mod_cast ho2
      nlinarith
    · have ho1' : (b65x_proj b : ℝ) < b65x_proj a := by exact_mod_cast ho1
      have ho2' : (b65x_auxMarkRe b : ℝ) < b65x_auxMarkRe a := by exact_mod_cast ho2
      nlinarith

include hp in
theorem b65x_aux_ne_base (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) (a : Fin 12) :
    b65x_aux p τ a ≠ mr_basePoint := by
  by_cases h1 : τ ≤ 1/3
  · simp only [b65x_aux, ite_eq_left h1]
    exact (b65x_config_injective p hp _ ⟨by linarith [hτ.1], by linarith⟩).2 a
  by_cases h2 : τ ≤ 2/3
  · obtain ⟨f, hf, e⟩ := b65x_aux_phase2 p τ h1 h2 a
    intro h
    rw [h, sub_self] at e
    have hc : b65b_track 0 a - mr_basePoint ≠ 0 := by
      intro h0
      have := (b65x_outer_rat a).2.1
      have h' := congrArg Complex.im h0
      simp [b65x_track0, mr_basePoint, mr_centre] at h'
      have : ((b65b_vertex0 a).2 : ℝ) + b65b_radius a < 10 := by exact_mod_cast this
      have hr : (0 : ℝ) < b65b_radius a := by exact_mod_cast (b65x_outer_rat a).2.2
      linarith
    exact hc ((mul_eq_zero.mp e.symm).resolve_left (by exact_mod_cast hf.ne'))
  · intro h
    have := congrArg Complex.im h
    simp only [b65x_aux, ite_eq_right h1, ite_eq_right h2] at this
    simp [b65x_marks_im, mr_basePoint, mr_centre] at this

end Witness

end HodgeLean.Foundations.Program
