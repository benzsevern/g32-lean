import HodgeLean.Foundations.Program.BraidBridgesThreeRelation
import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsFill

/-! # The isotopy marking

The rational normalization `M` is a Möbius homeomorphism of the sphere sending zero to infinity.
An extended configuration path moves the rationally normalized roots inside their discs to the
normalized roots, lifts the images of the apparent points `3, 1, −2, ∞` above the configuration,
and then follows the certified path. The end map of its isotopy composed with `M` is a
homeomorphism of the sphere minus the branch points onto the sphere minus the marks; it carries
the slot lassos to the transported loops, and the explicit curves pull back to regular loops.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex Set
namespace HodgeLean.Foundations.Program

/-- The rational box centres used by the rational normalization. -/
def b65x_ma : ℂ := ((b65b_boxCentre 0).1 : ℂ)
def b65x_mb : ℂ := ((b65b_boxCentre 6).1 : ℂ)

theorem b65x_ma_val : b65x_ma = ((-2220277/250000 : ℚ) : ℂ) := by
  simp [b65x_ma, b65b_boxCentre]

theorem b65x_mb_val : b65x_mb = ((-65683/100000 : ℚ) : ℂ) := by
  simp [b65x_mb, b65b_boxCentre]

theorem b65x_mab_ne : b65x_mb - b65x_ma ≠ 0 := by
  rw [b65x_ma_val, b65x_mb_val]; push_cast; norm_num

theorem b65x_ma_ne : b65x_ma ≠ 0 := by rw [b65x_ma_val]; push_cast; norm_num
theorem b65x_mb_ne : b65x_mb ≠ 0 := by rw [b65x_mb_val]; push_cast; norm_num

def b65x_alpha : ℂ := b65x_mb / (b65x_mb - b65x_ma)
def b65x_beta : ℂ := -(b65x_ma * b65x_mb) / (b65x_mb - b65x_ma)

theorem b65x_beta_ne : b65x_beta ≠ 0 := by
  unfold b65x_beta
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero b65x_ma_ne b65x_mb_ne)) b65x_mab_ne

/-- The affine part `z ↦ α + β z`. -/
def b65x_affine : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ b65x_beta b65x_beta_ne).trans (Homeomorph.addLeft b65x_alpha)

theorem b65x_affine_apply (z : ℂ) : b65x_affine z = b65x_alpha + b65x_beta * z := rfl

/-- The rational normalization as a homeomorphism of the sphere. -/
def b65x_mob : OnePoint ℂ ≃ₜ OnePoint ℂ := b65t_inv.trans b65x_affine.onePointCongr

theorem b65x_mob_coe {z : ℂ} (hz : z ≠ 0) :
    b65x_mob (z : OnePoint ℂ) = (b65s_normalize b65x_ma b65x_mb z : OnePoint ℂ) := by
  change OnePoint.map b65x_affine (b65t_inv (z : OnePoint ℂ)) = _
  rw [b65t_inv_apply, b65t_invFun_coe hz, OnePoint.map_some, b65x_affine_apply]
  congr 1
  unfold b65x_alpha b65x_beta b65s_normalize
  have h1 := b65x_mab_ne
  field_simp
  ring

theorem b65x_mob_zero : b65x_mob ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
  change OnePoint.map b65x_affine (b65t_inv ((0 : ℂ) : OnePoint ℂ)) = _
  rw [b65t_inv_apply, b65t_invFun_zero]; rfl

theorem b65x_mob_infty : b65x_mob OnePoint.infty = (b65x_alpha : OnePoint ℂ) := by
  change OnePoint.map b65x_affine (b65t_inv OnePoint.infty) = _
  rw [b65t_inv_apply, b65t_invFun_infty, OnePoint.map_some, b65x_affine_apply, mul_zero, add_zero]

/-- The rational normalization inverts the inverse normalization. -/
theorem b65x_mob_invN {w : ℂ}
    (hw : ((b65b_boxCentre 6).1 : ℂ) - w * (((b65b_boxCentre 6).1 : ℂ) -
      ((b65b_boxCentre 0).1 : ℂ)) ≠ 0) :
    b65x_mob (b65b_inverseNormalization w : OnePoint ℂ) = (w : OnePoint ℂ) := by
  have hw' : b65x_mb - w * (b65x_mb - b65x_ma) ≠ 0 := hw
  have hne : b65b_inverseNormalization w ≠ 0 := by
    simp only [b65b_inverseNormalization]
    exact div_ne_zero (mul_ne_zero b65x_ma_ne b65x_mb_ne) hw'
  rw [b65x_mob_coe hne]
  congr 1
  simp only [b65s_normalize, b65b_inverseNormalization]
  change (b65x_ma * b65x_mb / (b65x_mb - w * (b65x_mb - b65x_ma)) - b65x_ma) * b65x_mb /
    (b65x_ma * b65x_mb / (b65x_mb - w * (b65x_mb - b65x_ma)) * (b65x_mb - b65x_ma)) = w
  have h1 := b65x_mab_ne
  have h2 := b65x_ma_ne
  have h3 := b65x_mb_ne
  field_simp
  ring

/-- Images of the apparent points 3, 1, −2 and of infinity under the rational normalization. -/
def b65x_app : Fin 4 → ℚ :=
  ![(3 - (-2220277/250000)) * (-65683/100000) / (3 * ((-65683/100000) - (-2220277/250000))),
    (1 - (-2220277/250000)) * (-65683/100000) / (1 * ((-65683/100000) - (-2220277/250000))),
    (-2 - (-2220277/250000)) * (-65683/100000) / (-2 * ((-65683/100000) - (-2220277/250000))),
    (-65683/100000) / ((-65683/100000) - (-2220277/250000))]

/-- The apparent points of the source sphere. -/
def b65x_appSrc : Fin 4 → OnePoint ℂ :=
  ![((3 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ((-2 : ℂ) : OnePoint ℂ), OnePoint.infty]

theorem b65x_mob_app (k : Fin 4) :
    b65x_mob (b65x_appSrc k) = (((b65x_app k : ℝ) : ℂ) : OnePoint ℂ) := by
  fin_cases k
  · change b65x_mob ((3 : ℂ) : OnePoint ℂ) = _
    rw [b65x_mob_coe (by norm_num)]
    congr 1
    simp only [b65s_normalize, b65x_app, b65x_ma_val, b65x_mb_val]
    push_cast; norm_num
  · change b65x_mob ((1 : ℂ) : OnePoint ℂ) = _
    rw [b65x_mob_coe (by norm_num)]
    congr 1
    simp only [b65s_normalize, b65x_app, b65x_ma_val, b65x_mb_val]
    push_cast; norm_num
  · change b65x_mob ((-2 : ℂ) : OnePoint ℂ) = _
    rw [b65x_mob_coe (by norm_num)]
    congr 1
    simp only [b65s_normalize, b65x_app, b65x_ma_val, b65x_mb_val]
    push_cast; norm_num
  · change b65x_mob OnePoint.infty = _
    rw [b65x_mob_infty]
    congr 1
    simp only [b65x_alpha, b65x_app, b65x_ma_val, b65x_mb_val]
    push_cast; norm_num

theorem b65x_app_sep_rat : ∀ (k : Fin 4) (j : Fin 12),
    b65b_radius j < |b65x_app k - (b65b_vertex0 j).1| := by
  intro k j
  fin_cases k <;> fin_cases j <;> norm_num [b65x_app, b65b_radius, b65b_vertex0, lt_abs]

theorem b65x_app_inj_rat : ∀ k k' : Fin 4, k ≠ k' → b65x_app k ≠ b65x_app k' := by
  intro k k' h
  fin_cases k <;> fin_cases k' <;> first | exact absurd rfl h | norm_num [b65x_app]

theorem b65x_vertex_im_rat : ∀ j : Fin 12, |(b65b_vertex0 j).2| + b65b_radius j < 1 := by
  intro j
  fin_cases j <;> norm_num [b65b_vertex0, b65b_radius, abs_of_nonneg, abs_of_nonpos]

theorem b65x_app_curve_rat : ∀ (k : Fin 4) (m : Fin 12),
    -11/2 + (28/39 : ℚ) * (b65x_auxMarkRe m + 11/2) ≠ b65x_app k ∧
      (b65x_app k + 11/2) ^ 2 + 3 ^ 2 < 10 ^ 2 := by
  intro k m
  fin_cases k <;> fin_cases m <;> norm_num [b65x_app, b65x_auxMarkRe]

/-- The rational normalization of the roots. -/
def b65x_rnorm (p : Fin 12 → ℂ) (j : Fin 12) : ℂ := b65s_normalize b65x_ma b65x_mb (p j)

/-- The extended configuration path: twelve points, then the four lifted apparent points. -/
def b65x_ext (p : Fin 12 → ℂ) (τ : ℝ) (j : Fin 16) : ℂ :=
  if h : j.val < 12 then
    (if τ ≤ 1/2 then b65x_rnorm p ⟨j.val, h⟩ + ((2 * τ : ℝ) : ℂ) *
        (b65b_configuration p 0 ⟨j.val, h⟩ - b65x_rnorm p ⟨j.val, h⟩)
      else b65b_configuration p (2 * τ - 1) ⟨j.val, h⟩)
  else
    (if τ ≤ 1/2 then (((b65x_app ⟨j.val - 12, by omega⟩ : ℝ)) : ℂ) + ((2 * τ : ℝ) : ℂ) * (3 * I)
      else (((b65x_app ⟨j.val - 12, by omega⟩ : ℝ)) : ℂ) + 3 * I)

theorem b65x_ext_cfg (p : Fin 12 → ℂ) (τ : ℝ) (k : Fin 12) :
    b65x_ext p τ (Fin.castAdd 4 k) = if τ ≤ 1/2 then b65x_rnorm p k + ((2 * τ : ℝ) : ℂ) *
        (b65b_configuration p 0 k - b65x_rnorm p k) else b65b_configuration p (2 * τ - 1) k := by
  simp [b65x_ext]

theorem b65x_ext_app (p : Fin 12 → ℂ) (τ : ℝ) (k : Fin 4) :
    b65x_ext p τ (Fin.natAdd 12 k) = if τ ≤ 1/2 then (((b65x_app k : ℝ)) : ℂ) +
        ((2 * τ : ℝ) : ℂ) * (3 * I) else (((b65x_app k : ℝ)) : ℂ) + 3 * I := by
  simp [b65x_ext]

theorem b65x_ext_continuous (p : Fin 12 → ℂ) : Continuous (b65x_ext p) := by
  apply continuous_pi
  intro j
  unfold b65x_ext
  by_cases h : j.val < 12
  · simp only [dite_eq_left h]
    refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · exact (continuous_apply _).comp ((b65x_configuration_continuous p).comp (by fun_prop))
    · intro τ hτ; rw [hτ]; simp only [show 2 * (1/2 : ℝ) - 1 = 0 by norm_num]; push_cast; ring
  · simp only [dite_eq_right h]
    refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const ?_
    intro τ hτ; rw [hτ]; push_cast; ring

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
theorem b65x_rnorm_disc (j : Fin 12) : ‖b65x_rnorm p j - b65b_track 0 j‖ < b65b_radius j := by
  have hb := b65x_witness_box p hp j
  have e := b65b_normalization_enclosure (b65x_boxInv j) (p j) ((b65b_boxCentre 0).1 : ℝ)
    ((b65b_boxCentre 6).1 : ℝ) hb.1.le hb.2.1.le (by simp) (by simp)
  rw [b65x_boxIndex_boxInv] at e
  have h1 : (((b65b_boxCentre 0).1 : ℝ) : ℂ) = b65x_ma := by simp [b65x_ma]
  have h2 : (((b65b_boxCentre 6).1 : ℝ) : ℂ) = b65x_mb := by simp [b65x_mb]
  rw [h1, h2] at e
  exact e.2.2.2

include hp in
/-- Up to time one half each configuration point of the extended path is in its open disc. -/
theorem b65x_ext_disc (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/2)) (k : Fin 12) :
    ‖b65x_ext p τ (Fin.castAdd 4 k) - b65b_track 0 k‖ < b65b_radius k := by
  rw [b65x_ext_cfg, ite_eq_left hτ.2]
  have h1 := b65x_rnorm_disc p hp k
  have h2 := b65x_config_disc p hp 0 ⟨le_rfl, by norm_num⟩ k
  have e : b65x_rnorm p k + ((2 * τ : ℝ) : ℂ) * (b65b_configuration p 0 k - b65x_rnorm p k) -
      b65b_track 0 k = ((1 - 2 * τ : ℝ) : ℂ) * (b65x_rnorm p k - b65b_track 0 k) +
        ((2 * τ : ℝ) : ℂ) * (b65b_configuration p 0 k - b65b_track 0 k) := by push_cast; ring
  rw [e]
  have hl0 : 0 ≤ 2 * τ := by linarith [hτ.1]
  have hl1 : 0 ≤ 1 - 2 * τ := by linarith [hτ.2]
  calc _ ≤ ‖((1 - 2 * τ : ℝ) : ℂ) * (b65x_rnorm p k - b65b_track 0 k)‖ +
        ‖((2 * τ : ℝ) : ℂ) * (b65b_configuration p 0 k - b65b_track 0 k)‖ := norm_add_le _ _
    _ = (1 - 2 * τ) * ‖b65x_rnorm p k - b65b_track 0 k‖ +
        (2 * τ) * ‖b65b_configuration p 0 k - b65b_track 0 k‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hl1, abs_of_nonneg hl0]
    _ < b65b_radius k := by
      rcases hl0.lt_or_eq with h' | h'
      · nlinarith
      · rw [← h']; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact h1

theorem b65x_track_im (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (j : Fin 12) :
    |(b65b_track u j).im| < 1 := by
  have h := (Rat.cast_lt (K := ℝ)).mpr (b65x_vertex_im_rat j)
  push_cast at h
  have hr : (0 : ℝ) < b65b_radius j := by exact_mod_cast (b65x_outer_rat j).2.2
  have him : (b65b_track u j).im = (1 - u) * (b65b_vertex0 j).2 + u * (b65b_vertex1 j).2 := by
    simp [b65b_track]
  have h1 : ((b65b_vertex1 j).2 : ℝ) = 0 := by
    fin_cases j <;> simp [b65b_vertex1]
  rw [him, h1, mul_zero, add_zero, abs_mul, abs_of_nonneg (by linarith [hu.2])]
  nlinarith [abs_nonneg ((b65b_vertex0 j).2 : ℝ), hu.1]

include hp in
theorem b65x_ext_cfg_im (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) (k : Fin 12) :
    |(b65x_ext p τ (Fin.castAdd 4 k)).im| < 1 := by
  by_cases h : τ ≤ 1/2
  · have hd := b65x_ext_disc p hp τ ⟨hτ.1, h⟩ k
    have h1 := (Rat.cast_lt (K := ℝ)).mpr (b65x_vertex_im_rat k)
    push_cast at h1
    have h2 := Complex.abs_im_le_norm (b65x_ext p τ (Fin.castAdd 4 k) - b65b_track 0 k)
    have h3 : (b65b_track 0 k).im = (b65b_vertex0 k).2 := by simp [b65x_track0]
    have h4 := abs_sub_abs_le_abs_sub (b65x_ext p τ (Fin.castAdd 4 k)).im (b65b_track 0 k).im
    rw [Complex.sub_im] at h2
    rw [h3] at h4 h2
    linarith
  · push Not at h
    rw [b65x_ext_cfg, ite_eq_right (not_le.mpr h)]
    by_cases h' : 2 * τ - 1 ≤ 1/2
    · rw [b65b_configuration, ite_eq_left h']
      have hd := b65x_config_disc p hp (2 * τ - 1) ⟨by linarith, h'⟩ k
      rw [b65b_configuration, ite_eq_left h'] at hd
      have h1 := (Rat.cast_lt (K := ℝ)).mpr (b65x_vertex_im_rat k)
      push_cast at h1
      have h2 := Complex.abs_im_le_norm ((1 - 2 * ((2 * τ - 1 : ℝ) : ℂ)) *
        b65s_normalize (p 10) (p 11) (p k) + 2 * ((2 * τ - 1 : ℝ) : ℂ) * b65b_track 0 k -
          b65b_track 0 k)
      have h3 : (b65b_track 0 k).im = (b65b_vertex0 k).2 := by simp [b65x_track0]
      have h4 := abs_sub_abs_le_abs_sub ((1 - 2 * ((2 * τ - 1 : ℝ) : ℂ)) *
        b65s_normalize (p 10) (p 11) (p k) + 2 * ((2 * τ - 1 : ℝ) : ℂ) * b65b_track 0 k).im
          (b65b_track 0 k).im
      rw [Complex.sub_im] at h2
      rw [h3] at h4 h2
      linarith
    · push Not at h'
      rw [b65b_configuration, ite_eq_right (not_le.mpr h')]
      exact b65x_track_im _ ⟨by linarith, by linarith [hτ.2]⟩ k

theorem b65x_fin16_cases (j : Fin 16) :
    (∃ k : Fin 12, j = Fin.castAdd 4 k) ∨ (∃ k : Fin 4, j = Fin.natAdd 12 k) := by
  by_cases h : j.val < 12
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨j.val - 12, by omega⟩, Fin.ext (by simp; omega)⟩

include hp in
theorem b65x_ext_injective (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Function.Injective (b65x_ext p τ) ∧ ∀ j, b65x_ext p τ j ≠ mr_basePoint := by
  have happ_re : ∀ k : Fin 4, (b65x_ext p τ (Fin.natAdd 12 k)).re = b65x_app k := by
    intro k; rw [b65x_ext_app]; split_ifs <;> simp
  have happ_im : ∀ k : Fin 4, (b65x_ext p τ (Fin.natAdd 12 k)).im =
      if τ ≤ 1/2 then 2 * τ * 3 else 3 := by
    intro k; rw [b65x_ext_app]; split_ifs <;> simp
  have hcfg_app : ∀ (k : Fin 12) (k' : Fin 4),
      b65x_ext p τ (Fin.castAdd 4 k) ≠ b65x_ext p τ (Fin.natAdd 12 k') := by
    intro k k' he
    by_cases h : τ ≤ 1/2
    · have hd := b65x_ext_disc p hp τ ⟨hτ.1, h⟩ k
      have hre := congrArg Complex.re he
      rw [happ_re] at hre
      have h1 := Complex.abs_re_le_norm (b65x_ext p τ (Fin.castAdd 4 k) - b65b_track 0 k)
      rw [Complex.sub_re, hre] at h1
      have h2 := (Rat.cast_lt (K := ℝ)).mpr (b65x_app_sep_rat k' k)
      push_cast at h2
      have h3 : (b65b_track 0 k).re = (b65b_vertex0 k).1 := by simp [b65x_track0]
      rw [h3] at h1
      linarith
    · have him := congrArg Complex.im he
      rw [happ_im, ite_eq_right h] at him
      have := b65x_ext_cfg_im p hp τ hτ k
      rw [him] at this
      norm_num [abs_of_pos] at this
  constructor
  · intro i j hij
    rcases b65x_fin16_cases i with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rcases b65x_fin16_cases j with ⟨k', rfl⟩ | ⟨k', rfl⟩
      ·
        congr 1
        by_cases h : τ ≤ 1/2
        · by_contra hne
          have hsep := b65x_disc_sep k k' hne
          have h1 := b65x_ext_disc p hp τ ⟨hτ.1, h⟩ k
          have h2 := b65x_ext_disc p hp τ ⟨hτ.1, h⟩ k'
          rw [hij] at h1
          have := norm_sub_le_norm_sub_add_norm_sub (b65b_track 0 k)
            (b65x_ext p τ (Fin.castAdd 4 k')) (b65b_track 0 k')
          have e1 := norm_sub_rev (b65b_track 0 k) (b65x_ext p τ (Fin.castAdd 4 k'))
          linarith
        · push Not at h
          rw [b65x_ext_cfg, b65x_ext_cfg, ite_eq_right (not_le.mpr h), ite_eq_right (not_le.mpr h)] at hij
          exact (b65x_config_injective p hp (2 * τ - 1) ⟨by linarith, by linarith [hτ.2]⟩).1 hij
      · exact absurd hij (hcfg_app k k')
    · rcases b65x_fin16_cases j with ⟨k', rfl⟩ | ⟨k', rfl⟩
      · exact absurd hij.symm (hcfg_app k' k)
      · congr 1
        have hre := congrArg Complex.re hij
        rw [happ_re, happ_re] at hre
        by_contra hne
        exact b65x_app_inj_rat k k' hne (by exact_mod_cast hre)
  · intro j
    rcases b65x_fin16_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · intro he
      have him := b65x_ext_cfg_im p hp τ hτ k
      rw [he] at him
      simp [mr_basePoint, mr_centre] at him
    · intro he
      have him := congrArg Complex.im he
      rw [happ_im] at him
      simp [mr_basePoint, mr_centre] at him
      split_ifs at him <;> nlinarith [hτ.1, hτ.2]

end Witness

/-- Real parts of the marks. -/
def b65x_markRe : Fin 12 → ℚ := ![-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, 0, 1]

theorem b65x_markRe_eq (m : Fin 12) : (mr_marks m).re = (b65x_markRe m : ℝ) := by
  fin_cases m <;> norm_num [b65x_markRe, mr_marks, mr_base, Fin.append, Fin.addCases]

theorem b65x_app_curve2_rat : ∀ (k : Fin 4) (m : Fin 12),
    -11/2 + (28/39 : ℚ) * (b65x_markRe m + 11/2) ≠ b65x_app k := by
  intro k m
  fin_cases k <;> fin_cases m <;> norm_num [b65x_app, b65x_markRe]

/-- The explicit curves miss the lifted apparent points. -/
theorem b65x_curve_avoid_app (i : Fin 13) (s : unitInterval) (k : Fin 4) :
    mr_curve i s ≠ ((((b65x_app k : ℝ)) : ℂ) + 3 * I : OnePoint ℂ) := by
  have hout := (Rat.cast_lt (K := ℝ)).mpr (b65x_app_curve_rat k 0).2
  push_cast at hout
  unfold mr_curve
  split_ifs with hi
  · intro he
    have he' := OnePoint.coe_injective he
    rw [b65x_mr_lasso_shape] at he'
    rcases b65x_shape_cases _ _ s ⟨s.2.1, s.2.2⟩ with ⟨μ, hμ, hseg⟩ | hcirc
    · rw [hseg] at he'
      have him := congrArg Complex.im he'
      have hre := congrArg Complex.re he'
      rw [b65x_seg_im] at him
      simp only [Complex.add_im, Complex.div_im, b65x_marks_im] at him
      simp at him
      have hμv : μ = 28/39 := by linarith
      simp [mr_basePoint, mr_centre, b65x_markRe_eq] at hre
      rw [hμv] at hre
      have := b65x_app_curve2_rat k ⟨i.val, hi⟩
      apply this
      exact Rat.cast_injective (α := ℝ) (by push_cast; linarith)
    · rw [he'] at hcirc
      have h1 := Complex.abs_im_le_norm ((((b65x_app k : ℝ)) : ℂ) + 3 * I - mr_marks ⟨i.val, hi⟩)
      rw [hcirc] at h1
      simp [b65x_marks_im] at h1
      norm_num at h1
  · intro he
    have he' := OnePoint.coe_injective he
    have h2 := b65x_outer_norm s
    rw [he'] at h2
    have hn : ‖(((b65x_app k : ℝ)) : ℂ) + 3 * I + 11/2‖ ^ 2 = ((b65x_app k : ℝ) + 11/2) ^ 2 + 3 ^ 2 := by
      rw [b65x_norm_sq]; simp
    have : ‖(((b65x_app k : ℝ)) : ℂ) + 3 * I + 11/2‖ < 10 := by
      apply lt_of_pow_lt_pow_left₀ 2 (by norm_num); rw [hn]; linarith
    linarith

/-- A homomorphism on the fundamental group of a homeomorphic space, transported along the
homeomorphism and a base point identity. -/
theorem b65x_transfer_hom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : Y ≃ₜ X)
    (y : Y) (x0 : X) (hx : h y = x0) (ρ : FundamentalGroup X x0 →* b4b_Group) :
    ∃ χ : FundamentalGroup Y y →* b4b_Group, ∀ c : Path y y,
      χ (FundamentalGroup.fromPath ⟦c⟧) =
        ρ (FundamentalGroup.fromPath ⟦(c.map h.continuous).cast hx.symm hx.symm⟧) := by
  subst hx
  obtain ⟨E, hE⟩ := RiemannRochTop_homeomorph_pi1_map h y
  refine ⟨ρ.comp E.toMonoidHom, fun c ↦ ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Path.cast_rfl_rfl]
  exact congrArg ρ (hE c)

/-- Reparametrization of time that waits until one half. -/
def b65x_late (τ : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (2 * (τ : ℝ) - 1)

theorem b65x_late_continuous : Continuous b65x_late :=
  continuous_projIcc.comp (by fun_prop)

theorem b65x_late_of_le {τ : unitInterval} (h : (τ : ℝ) ≤ 1/2) : b65x_late τ = 0 := by
  apply Subtype.ext
  simp only [b65x_late, Set.Icc.coe_zero]
  rw [Set.projIcc_of_le_left _ (by linarith)]

theorem b65x_late_of_gt {τ : unitInterval} (h : 1/2 < (τ : ℝ)) :
    (b65x_late τ : ℝ) = 2 * (τ : ℝ) - 1 := by
  simp only [b65x_late]
  rw [Set.projIcc_of_mem]
  exact ⟨by linarith, by linarith [τ.2.2]⟩

theorem b65x_late_one : b65x_late 1 = 1 := by
  apply Subtype.ext
  rw [b65x_late_of_gt (by simp; norm_num)]
  simp; norm_num

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
/-- The isotopy marking. -/
theorem b65x_isotopy_marking_body (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s)) :
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base, ∃ γ : Fin 13 → Path x x,
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      ∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∃ χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group,
          (∀ i, χ (b63gP_loops i) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i⟧))) ∧
          ∀ j, χ (FundamentalGroup.fromPath ⟦κ₁ j⟧) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦δ j⟧)) := by
  -- transport along the extended path
  have hQc := b65x_ext_continuous p
  obtain ⟨e, heB, heI, heQ, hfam⟩ := b65x_transportS (b65x_ext p) hQc
    (fun t ht ↦ (b65x_ext_injective p hp t ht).1) (fun t ht ↦ (b65x_ext_injective p hp t ht).2)
    (Set.range (Fin.castAdd 4))
  have hQ0c : ∀ k : Fin 12, b65x_ext p 0 (Fin.castAdd 4 k) = b65x_rnorm p k := by
    intro k; rw [b65x_ext_cfg]; simp
  have hQ1c : ∀ k : Fin 12, b65x_ext p 1 (Fin.castAdd 4 k) = mr_marks k := by
    intro k; rw [b65x_ext_cfg, ite_eq_right (by norm_num)]
    rw [show (2 * 1 - 1 : ℝ) = 1 by norm_num, b65x_configuration_one]
  have hQ0a : ∀ k : Fin 4, b65x_ext p 0 (Fin.natAdd 12 k) = ((b65x_app k : ℝ) : ℂ) := by
    intro k; rw [b65x_ext_app]; simp
  have hQ1a : ∀ k : Fin 4, b65x_ext p 1 (Fin.natAdd 12 k) = ((b65x_app k : ℝ) : ℂ) + 3 * I := by
    intro k; rw [b65x_ext_app, ite_eq_right (by norm_num)]
  let H : OnePoint ℂ ≃ₜ OnePoint ℂ := b65x_mob.trans e
  have hH : ∀ w, H w = e (b65x_mob w) := fun w ↦ rfl
  have hH0 : H ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by rw [hH, b65x_mob_zero, heI]
  have hHp : ∀ j, H (p j : OnePoint ℂ) = (mr_marks j : OnePoint ℂ) := by
    intro j
    rw [hH, b65x_mob_coe (b65x_witness_ne_zero p hp j)]
    have := heQ (Fin.castAdd 4 j)
    rw [hQ0c, hQ1c] at this
    exact this
  have hHapp : ∀ k, H (b65x_appSrc k) = ((((b65x_app k : ℝ) : ℂ) + 3 * I : ℂ) : OnePoint ℂ) := by
    intro k
    rw [hH, b65x_mob_app]
    have := heQ (Fin.natAdd 12 k)
    rw [hQ0a, hQ1a] at this
    exact this
  have hHinv : ∀ j : Fin 13, ∀ s : unitInterval,
      H (b65b_inverseNormalization (b65b_lasso (b65x_slot j) s) : OnePoint ℂ) =
        e (b65b_lasso (b65x_slot j) s : OnePoint ℂ) := by
    intro j s
    have hreg : b65b_inverseNormalization (b65b_lasso (b65x_slot j) s) ∈ b65s_regular := by
      rw [← hδ]; exact (δ j s).2
    rw [hH, b65x_mob_invN (b65x_invN_denom hreg)]
  have hxval : x.val = b65b_inverseNormalization mr_basePoint := by
    have := hδ 0 0
    rw [(δ 0).source, Set.Icc.coe_zero, b65x_lasso_zero] at this
    exact this
  have hHx : H (x.val : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ) := by
    have := hHinv 0 0
    rw [Set.Icc.coe_zero, b65x_lasso_zero, heB] at this
    rw [hxval]; exact this
  -- the homeomorphism of the punctured spheres
  have hroot : ∀ j, b65r_P 5 (p j) = 0 ∨ b65r_P (-7) (p j) = 0 := by
    intro j
    have hb := (b65x_witness_box p hp j).2.2
    have hf : b65b_boxFibre (b65x_boxInv j) = 5 ∨ b65b_boxFibre (b65x_boxInv j) = -7 := by
      generalize b65x_boxInv j = k
      fin_cases k <;> norm_num [b65b_boxFibre]
    rcases hf with hf | hf
    · rw [hf] at hb; left; exact_mod_cast hb
    · rw [hf] at hb; right; exact_mod_cast hb
  have hmem : ∀ w, w ∈ b65s_sphere ↔ H w ∈ b6t_punctured mr_base := by
    intro w
    constructor
    · intro hw ⟨k, hk⟩
      induction k using Fin.lastCases with
      | last =>
        have : H w = H ((0 : ℂ) : OnePoint ℂ) := by rw [hH0, ← hk]; rfl
        rw [H.injective this] at hw
        exact hw ⟨0, rfl, Or.inl rfl⟩
      | cast j =>
        rw [b65x_branch_cast] at hk
        rw [← hHp j] at hk
        rw [← H.injective hk] at hw
        exact hw ⟨p j, rfl, Or.inr (hroot j)⟩
    · intro hw ⟨z, hz, hzb⟩
      subst hz
      rcases b65x_witness_exhaust p hp z hzb with h0 | ⟨j, hj⟩
      · subst h0; rw [hH0] at hw; exact hw ⟨Fin.last 12, rfl⟩
      · subst hj; rw [hHp] at hw; exact hw ⟨j.castSucc, b65x_branch_cast j⟩
  let h : b65s_sphere ≃ₜ b6t_punctured mr_base := H.subtype hmem
  have hhv : ∀ w : b65s_sphere, ((h w : b6t_punctured mr_base) : OnePoint ℂ) = H w := fun w ↦ rfl
  have hhsv : ∀ w : b6t_punctured mr_base, ((h.symm w : b65s_sphere) : OnePoint ℂ) = H.symm w :=
    fun w ↦ rfl
  -- the pulled-back curves
  have hcF : ∀ i (s : unitInterval), H.symm (mr_curve i s) ∈ b65s_sphere \ (b65t_F : Set (OnePoint ℂ)) := by
    intro i s
    have hin : H (H.symm (mr_curve i s)) ∈ b6t_punctured mr_base := by
      rw [H.apply_symm_apply]
      exact (mr_curve_avoids mr_base b63gP_s₀.property i s).1
    refine ⟨(hmem _).mpr hin, fun hF ↦ ?_⟩
    have hF' : H.symm (mr_curve i s) = b65x_appSrc 0 ∨ H.symm (mr_curve i s) = b65x_appSrc 1 ∨
        H.symm (mr_curve i s) = b65x_appSrc 2 ∨ H.symm (mr_curve i s) = b65x_appSrc 3 := by
      simpa [b65t_F, b65x_appSrc] using hF
    rcases hF' with h' | h' | h' | h' <;>
    · have := congrArg H h'
      rw [H.apply_symm_apply, hHapp] at this
      exact b65x_curve_avoid_app i s _ this
  have hBF : H.symm (mr_basePoint : OnePoint ℂ) = (x.val : OnePoint ℂ) := by
    rw [← hHx, H.symm_apply_apply]
  let zF : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ))) := b65t_chart x
  have hzF : ∀ i, (⟨H.symm (mr_curve i 0), hcF i 0⟩ : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ)))) =
      zF := by
    intro i; apply Subtype.ext
    change H.symm (mr_curve i 0) = (x.val : OnePoint ℂ)
    rw [mr_curve_zero, hBF]
  have hzF1 : ∀ i, (⟨H.symm (mr_curve i 1), hcF i 1⟩ : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ)))) =
      zF := by
    intro i; apply Subtype.ext
    change H.symm (mr_curve i 1) = (x.val : OnePoint ℂ)
    rw [mr_curve_one, hBF]
  let pF : Fin 13 → Path zF zF := fun i ↦
    { toFun := fun s ↦ ⟨H.symm (mr_curve i s), hcF i s⟩
      continuous_toFun := (H.symm.continuous.comp ((mr_curve_continuous i).comp
        continuous_subtype_val)).subtype_mk _
      source' := hzF i
      target' := hzF1 i }
  let γ : Fin 13 → Path x x := fun i ↦ (pF i).map b65t_unchart.continuous
  have hγv : ∀ i s, ((b65s_inclusion (γ i s) : b65s_sphere) : OnePoint ℂ) = H.symm (mr_curve i s) := by
    intro i s
    exact (b65t_elim_mem (pF i s)).2
  refine ⟨h, γ, fun i s ↦ ?_, fun i s ↦ ?_, fun ρ ↦ ?_⟩
  · rw [hhv, hγv, H.apply_symm_apply]
  · have hnF := (hcF i s).2
    have hv : ((γ i s).val : OnePoint ℂ) = H.symm (mr_curve i s) := hγv i s
    refine ⟨fun h3 ↦ hnF ?_, fun h1 ↦ hnF ?_, fun h2 ↦ hnF ?_, OnePoint.coe_ne_infty _⟩
    · rw [← hv, h3]; simp [b65t_F]
    · rw [← hv, h1]; simp [b65t_F]
    · rw [← hv, h2]; simp [b65t_F]
  -- the marking
  have hx0 : h.symm b63gP_basePoint = b65s_inclusion x := by
    apply Subtype.ext
    rw [hhsv]
    change H.symm (mr_basePoint : OnePoint ℂ) = (x.val : OnePoint ℂ)
    exact hBF
  obtain ⟨χ, hχ⟩ := b65x_transfer_hom h.symm b63gP_basePoint (b65s_inclusion x) hx0 ρ
  refine ⟨χ, fun i ↦ ?_, fun j ↦ ?_⟩
  · let M : Path b63gP_basePoint b63gP_basePoint := b65x_mkPath _ _ (mr_curve i ·)
      ((mr_curve_continuous _).comp continuous_subtype_val)
      (fun s ↦ (mr_curve_avoids mr_base b63gP_s₀.property i s).1)
      (mr_curve_zero _) (mr_curve_one _)
    rw [← b65x_loops_eq i M (fun s ↦ rfl), hχ]
    have hpe : (M.map h.symm.continuous).cast hx0.symm hx0.symm =
        (γ i).map b65s_inclusion.continuous := by
      apply Path.ext; funext s; apply Subtype.ext
      change H.symm (mr_curve i s) = ((b65s_inclusion (γ i s) : b65s_sphere) : OnePoint ℂ)
      rw [hγv]
    rw [hpe]; rfl
  · -- the transported lasso
    have hb : h (b65s_inclusion x) = b63gP_basePoint := by
      apply Subtype.ext; rw [hhv]; exact hHx
    let T : Path b63gP_basePoint b63gP_basePoint :=
      (((δ j).map b65s_inclusion.continuous).map h.continuous).cast hb.symm hb.symm
    have hTv : ∀ s, (T s : OnePoint ℂ) = e (b65b_lasso (b65x_slot j) s : OnePoint ℂ) := by
      intro s
      change H ((δ j s).val : OnePoint ℂ) = _
      rw [hδ, hHinv]
    let Kx : C(unitInterval × unitInterval, OnePoint ℂ) :=
      ⟨fun q ↦ K j (b65x_late q.1, q.2), (K j).continuous.comp
        ((b65x_late_continuous.comp continuous_fst).prodMk continuous_snd)⟩
    have hTκ : T.Homotopic (κ₁ j) := by
      apply hfam Kx _ _ _ _ (κ₁ j) T
      · intro s; rw [hκ₁]; change K j (1, s) = K j (b65x_late 1, s); rw [b65x_late_one]
      · intro s; rw [hTv]; change _ = e (K j (b65x_late 0, s))
        rw [b65x_late_of_le (by simp), hK0]
      · intro t; exact hKb j (b65x_late t)
      · intro t s
        refine ⟨(hKa j _ s).1, ?_⟩
        rintro _ ⟨k, rfl⟩
        by_cases ht : (t : ℝ) ≤ 1/2
        · change K j (b65x_late t, s) ≠ _
          rw [b65x_late_of_le ht, hK0]
          intro he
          exact b65x_lasso_avoid _ s ⟨s.2.1, s.2.2⟩ k _ (b65x_ext_disc p hp t ⟨t.2.1, ht⟩ k)
            (OnePoint.coe_injective he)
        · push Not at ht
          change K j (b65x_late t, s) ≠ _
          rw [b65x_ext_cfg, ite_eq_right (not_le.mpr ht)]
          have := (hKa j (b65x_late t) s).2 k
          rwa [b65x_late_of_gt ht] at this
      · intro w hw hj
        apply b65x_mem_punctured hw
        intro k
        have := hj (Fin.castAdd 4 k) ⟨k, rfl⟩
        rwa [hQ1c] at this
    have hcl : FundamentalGroup.fromPath ⟦κ₁ j⟧ = FundamentalGroup.fromPath ⟦T⟧ :=
      (congrArg FundamentalGroup.fromPath (Quotient.sound hTκ)).symm
    rw [hcl, hχ]
    have hpe : (T.map h.symm.continuous).cast hx0.symm hx0.symm =
        (δ j).map b65s_inclusion.continuous := by
      apply Path.ext; funext s; apply Subtype.ext
      change H.symm (H ((δ j s).val : OnePoint ℂ)) = _
      rw [H.symm_apply_apply]
      rfl
    rw [hpe]; rfl

end Witness

end HodgeLean.Foundations.Program
