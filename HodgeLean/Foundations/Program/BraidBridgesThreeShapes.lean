import HodgeLean.Foundations.Program.BraidBridgesThreeMoving

/-! # Lasso shapes, radial lassos and static homotopies

A lasso shape runs from the base point to `c + w`, around the circle about `c` through that
point, and back. The certified lassos, the explicit `mr_lasso` curves and the radial lassos
`c + ρ (B - c)` are lasso shapes. Families of shapes avoiding a finite set give based homotopies.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex Set
namespace HodgeLean.Foundations.Program

/-- The lasso shape about `c` through `c + w`. -/
def b65x_shape (c w : ℂ) (s : ℝ) : ℂ :=
  if s ≤ 1/3 then mr_basePoint + ((3 * s : ℝ) : ℂ) * (c + w - mr_basePoint)
  else if s ≤ 2/3 then c + w * cexp (2 * Real.pi * I * ((3 * s - 1 : ℝ) : ℂ))
  else mr_basePoint + ((3 - 3 * s : ℝ) : ℂ) * (c + w - mr_basePoint)

theorem b65x_shape_zero (c w : ℂ) : b65x_shape c w 0 = mr_basePoint := by
  simp [b65x_shape]

theorem b65x_shape_one (c w : ℂ) : b65x_shape c w 1 = mr_basePoint := by
  simp only [b65x_shape]
  rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
  simp

theorem b65x_shape_continuous :
    Continuous fun q : ℂ × ℂ × ℝ ↦ b65x_shape q.1 q.2.1 q.2.2 := by
  unfold b65x_shape
  refine Continuous.if_le (by fun_prop) (Continuous.if_le (by fun_prop) (by fun_prop)
    (by fun_prop) continuous_const ?_) (by fun_prop) continuous_const ?_
  · rintro ⟨c, w, s⟩ hs
    simp only at hs ⊢
    rw [hs]
    have : 2 * (Real.pi : ℂ) * I * (((3 * (2/3 : ℝ) - 1 : ℝ)) : ℂ) = 2 * Real.pi * I := by
      push_cast; ring
    rw [this, Complex.exp_two_pi_mul_I]
    push_cast; ring
  · rintro ⟨c, w, s⟩ hs
    simp only at hs ⊢
    rw [hs, ite_eq_left (by norm_num)]
    have : 2 * (Real.pi : ℂ) * I * (((3 * (1/3 : ℝ) - 1 : ℝ)) : ℂ) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero]
    push_cast; ring

/-- A lasso shape is on the segment to `c + w` or on the circle about `c` of radius `‖w‖`. -/
theorem b65x_shape_cases (c w : ℂ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∃ μ ∈ Icc (0 : ℝ) 1, b65x_shape c w s = mr_basePoint + (μ : ℂ) * (c + w - mr_basePoint)) ∨
      ‖b65x_shape c w s - c‖ = ‖w‖ := by
  unfold b65x_shape
  split_ifs with h1 h2
  · exact Or.inl ⟨3 * s, ⟨by linarith [hs.1], by linarith⟩, rfl⟩
  · right
    rw [add_sub_cancel_left, norm_mul, Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * I * ((3 * s - 1 : ℝ) : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one]
  · exact Or.inl ⟨3 - 3 * s, ⟨by linarith [hs.2], by linarith⟩, rfl⟩

theorem b65x_shape_avoid {c w v : ℂ} (hc : ‖v - c‖ ≠ ‖w‖)
    (hseg : ∀ μ ∈ Icc (0 : ℝ) 1, mr_basePoint + (μ : ℂ) * (c + w - mr_basePoint) ≠ v)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : b65x_shape c w s ≠ v := by
  rcases b65x_shape_cases c w s hs with ⟨μ, hμ, he⟩ | he
  · rw [he]; exact hseg μ hμ
  · intro h; rw [h] at he; exact hc he

theorem b65x_lasso_shape (col : Fin 13) (hc : col.val ≠ 0) (s : ℝ) :
    b65b_lasso col s = b65x_shape (b65b_track 0 (b65x_colDisc col hc))
      (I * ((b65b_radius (b65x_colDisc col hc) : ℝ) : ℂ)) s := by
  unfold b65b_lasso b65x_shape
  rw [dite_eq_right hc]
  simp only [Complex.ofReal_ratCast]
  push_cast
  rfl

theorem b65x_mr_lasso_shape (m : ℂ) (s : ℝ) : mr_lasso m s = b65x_shape m (I / 4) s := by
  unfold mr_lasso b65x_shape
  rfl

/-- The cross product of two plane vectors. -/
def b65x_cross (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

theorem b65x_cross_abs_le (a b : ℂ) : |b65x_cross a b| ≤ ‖a‖ * ‖b‖ := b65x_cross_le a b

theorem b65x_cross_seg (w μ : ℂ) (hμ : μ.im = 0) :
    b65x_cross (w - mr_basePoint) (mr_basePoint + μ * (w - mr_basePoint) - mr_basePoint) = 0 := by
  simp only [b65x_cross, add_sub_cancel_left, Complex.mul_re, Complex.mul_im, hμ]
  ring

theorem b65x_cone_robust_rat : ∀ j k : Fin 12, j ≠ k →
    (13 * (b65b_radius j + b65b_radius k) + b65b_radius j * b65b_radius k) ^ 2 <
      (((b65b_vertex0 j).1 + 11/2) * ((b65b_vertex0 k).2 - 10) -
        ((b65b_vertex0 j).2 - 10) * ((b65b_vertex0 k).1 + 11/2)) ^ 2 := by
  intro j k h
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd rfl h
    | norm_num [b65b_radius, b65b_vertex0]

theorem b65x_centre_far_rat : ∀ j : Fin 12,
    ((b65b_vertex0 j).1 + 11/2) ^ 2 + ((b65b_vertex0 j).2 - 10) ^ 2 ≤ 13 ^ 2 := by
  intro j
  fin_cases j <;> norm_num [b65b_vertex0]

/-- Points of two different closed lasso discs are on different rays from the base point. -/
theorem b65x_cone_robust (j k : Fin 12) (h : j ≠ k) (w v : ℂ)
    (hw : ‖w - b65b_track 0 j‖ ≤ b65b_radius j) (hv : ‖v - b65b_track 0 k‖ ≤ b65b_radius k) :
    b65x_cross (w - mr_basePoint) (v - mr_basePoint) ≠ 0 := by
  intro hcr
  set uj := b65b_track 0 j - mr_basePoint
  set uk := b65b_track 0 k - mr_basePoint
  set a := w - b65b_track 0 j
  set b := v - b65b_track 0 k
  have hdec : b65x_cross (w - mr_basePoint) (v - mr_basePoint) =
      b65x_cross uj uk + b65x_cross uj b + b65x_cross a uk + b65x_cross a b := by
    simp only [b65x_cross, uj, uk, a, b, Complex.sub_re, Complex.sub_im]; ring
  have hcone := (Rat.cast_lt (K := ℝ)).mpr (b65x_cone_robust_rat j k h)
  push_cast at hcone
  have hcuu : b65x_cross uj uk = (((b65b_vertex0 j).1 : ℝ) + 11/2) * ((b65b_vertex0 k).2 - 10) -
      (((b65b_vertex0 j).2 : ℝ) - 10) * ((b65b_vertex0 k).1 + 11/2) := by
    simp only [b65x_cross, uj, uk, b65x_track0, mr_basePoint, mr_centre]; simp; ring
  have hfar : ∀ i : Fin 12, ‖b65b_track 0 i - mr_basePoint‖ ≤ 13 := by
    intro i
    have h1 := (Rat.cast_le (K := ℝ)).mpr (b65x_centre_far_rat i)
    push_cast at h1
    apply le_of_pow_le_pow_left₀ two_ne_zero (by norm_num)
    rw [b65x_norm_sq]
    simp [b65x_track0, mr_basePoint, mr_centre]
    nlinarith [h1]
  have hrj : (0 : ℝ) ≤ b65b_radius j := by exact_mod_cast (b65x_outer_rat j).2.2.le
  have hrk : (0 : ℝ) ≤ b65b_radius k := by exact_mod_cast (b65x_outer_rat k).2.2.le
  have h1 := b65x_cross_abs_le uj b
  have h2 := b65x_cross_abs_le a uk
  have h3 := b65x_cross_abs_le a b
  have e1 : ‖uj‖ * ‖b‖ ≤ 13 * b65b_radius k :=
    mul_le_mul (hfar j) hv (norm_nonneg _) (by norm_num)
  have e2 : ‖a‖ * ‖uk‖ ≤ b65b_radius j * 13 :=
    mul_le_mul hw (hfar k) (norm_nonneg _) hrj
  have e3 : ‖a‖ * ‖b‖ ≤ b65b_radius j * b65b_radius k :=
    mul_le_mul hw hv (norm_nonneg _) hrj
  rw [hcr] at hdec
  have hsum : |b65x_cross uj uk| ≤
      13 * (b65b_radius j + b65b_radius k) + b65b_radius j * b65b_radius k := by
    have : b65x_cross uj uk = -(b65x_cross uj b + b65x_cross a uk + b65x_cross a b) := by
      linarith
    rw [this, abs_neg]
    calc |b65x_cross uj b + b65x_cross a uk + b65x_cross a b|
        ≤ |b65x_cross uj b| + |b65x_cross a uk| + |b65x_cross a b| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  rw [hcuu] at hsum
  have hpos : (0 : ℝ) ≤ 13 * (b65b_radius j + b65b_radius k) + b65b_radius j * b65b_radius k := by
    positivity
  have := sq_le_sq' (by linarith [neg_abs_le ((((b65b_vertex0 j).1 : ℝ) + 11/2) *
      ((b65b_vertex0 k).2 - 10) - (((b65b_vertex0 j).2 : ℝ) - 10) * ((b65b_vertex0 k).1 + 11/2))])
    (le_trans (le_abs_self _) hsum)
  linarith

/-- Based homotopy from a continuous family of based loops in a subset of the sphere. -/
theorem b65x_homotopic_of_family {Y : Set (OnePoint ℂ)} {y : Y} (γ γ' : Path y y)
    (F : unitInterval × unitInterval → OnePoint ℂ) (hF : Continuous F) (hY : ∀ q, F q ∈ Y)
    (h0 : ∀ s, F (0, s) = γ s) (h1 : ∀ s, F (1, s) = γ' s)
    (hb : ∀ t, F (t, 0) = y ∧ F (t, 1) = y) : γ.Homotopic γ' :=
  ⟨{ toFun := fun q ↦ ⟨F q, hY q⟩
     continuous_toFun := hF.subtype_mk _
     map_zero_left := fun s ↦ Subtype.ext (h0 s)
     map_one_left := fun s ↦ Subtype.ext (h1 s)
     prop' := fun t s hs ↦ by
       rcases hs with rfl | rfl
       · exact Subtype.ext ((hb t).1.trans (γ.source.symm ▸ rfl))
       · exact Subtype.ext ((hb t).2.trans (γ.target.symm ▸ rfl)) }⟩

/-- Small radial lassos about a point that no other point blocks avoid the whole configuration. -/
theorem b65x_radial_valid (Q : ℝ → Fin 12 → ℂ) (hQ : Continuous Q) (a : Fin 12)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b, b ≠ a → ∀ μ ∈ Icc (0 : ℝ) 1,
      mr_basePoint + (μ : ℂ) * (Q t a - mr_basePoint) ≠ Q t b)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, Q t a ≠ mr_basePoint) :
    ∃ ρ0 > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ b,
      b65x_shape (Q t a) ((ρ : ℂ) * (mr_basePoint - Q t a)) s ≠ Q t b := by
  -- separation from the other points
  have hpair : ∀ b : {b : Fin 12 // b ≠ a}, ∃ m > 0, ∀ t ∈ Icc (0 : ℝ) 1,
      m ≤ ‖Q t b.1 - Q t a‖ := by
    rintro ⟨b, hb⟩
    have hc : ContinuousOn (fun t ↦ ‖Q t b - Q t a‖) (Icc 0 1) :=
      (((continuous_apply b).comp hQ).sub ((continuous_apply a).comp hQ)).norm.continuousOn
    obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hc
    refine ⟨‖Q t0 b - Q t0 a‖, norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ ?_), fun t ht ↦ hmin ht⟩
    exact hseg t0 ht0 b hb 1 ⟨zero_le_one, le_rfl⟩ (by rw [h]; push_cast; ring)
  choose m hm hmle using hpair
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ b, δ ≤ m b := by
    have : Nonempty {b : Fin 12 // b ≠ a} := by
      by_cases h : a = 0
      · exact ⟨⟨1, by rw [h]; decide⟩⟩
      · exact ⟨⟨0, Ne.symm h⟩⟩
    obtain ⟨b0, hb0⟩ := Finite.exists_min m
    exact ⟨m b0, hm b0, hb0⟩
  obtain ⟨M, hM, hMle⟩ : ∃ M > 0, ∀ t ∈ Icc (0 : ℝ) 1, ‖mr_basePoint - Q t a‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.image
      (continuous_const.sub ((continuous_apply a).comp hQ))).isBounded.exists_norm_le
    exact ⟨max C 1, by positivity, fun t ht ↦ (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)⟩
  refine ⟨min (1/2) (δ / (2 * M)), by positivity, fun ρ hρ hρ0 t ht s hs b ↦ ?_⟩
  have hρ1 : ρ ≤ 1/2 := hρ0.trans (min_le_left _ _)
  have hρ2 : ρ ≤ δ / (2 * M) := hρ0.trans (min_le_right _ _)
  have hw : ‖(ρ : ℂ) * (mr_basePoint - Q t a)‖ = ρ * ‖mr_basePoint - Q t a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hseg' : ∀ μ : ℝ, mr_basePoint + (μ : ℂ) * (Q t a + (ρ : ℂ) * (mr_basePoint - Q t a) -
      mr_basePoint) = mr_basePoint + ((μ * (1 - ρ) : ℝ) : ℂ) * (Q t a - mr_basePoint) := by
    intro μ; push_cast; ring
  apply b65x_shape_avoid _ _ s hs
  · rw [hw]
    by_cases hba : b = a
    · subst hba
      rw [sub_self, norm_zero]
      exact (mul_pos hρ (norm_pos_iff.mpr (sub_ne_zero.mpr (hB t ht).symm))).ne
    · have h1 := (hδle ⟨b, hba⟩).trans (hmle ⟨b, hba⟩ t ht)
      have h2 : ρ * ‖mr_basePoint - Q t a‖ ≤ δ / (2 * M) * M :=
        mul_le_mul hρ2 (hMle t ht) (norm_nonneg _) (by positivity)
      have h3 : δ / (2 * M) * M = δ / 2 := by field_simp
      intro he
      linarith
  · intro μ hμ
    rw [hseg']
    have hμ' : μ * (1 - ρ) ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hμ.1 (by linarith), by nlinarith [hμ.1, hμ.2]⟩
    by_cases hba : b = a
    · subst hba
      intro he
      have h1 : ((μ * (1 - ρ) - 1 : ℝ) : ℂ) * (Q t b - mr_basePoint) = 0 := by
        push_cast at he ⊢; linear_combination he
      rcases mul_eq_zero.mp h1 with h | h
      · have : μ * (1 - ρ) - 1 = 0 := by exact_mod_cast h
        nlinarith [hμ.1, hμ.2]
      · exact hB t ht (sub_eq_zero.mp h)
    · exact hseg t ht b hba _ hμ'

/-- A shape whose circle lies in the closed `k`-th disc and which misses the `k`-th point avoids
every point of a configuration with one point in each open disc. -/
theorem b65x_disc_shape_avoid (k : Fin 12) (Q0 : Fin 12 → ℂ)
    (hQ : ∀ j, ‖Q0 j - b65b_track 0 j‖ < b65b_radius j) (c w : ℂ)
    (h1 : ‖c - b65b_track 0 k‖ + ‖w‖ ≤ b65b_radius k) (h2 : ‖Q0 k - c‖ ≠ ‖w‖)
    (h3 : ∀ μ ∈ Icc (0 : ℝ) 1, mr_basePoint + (μ : ℂ) * (c + w - mr_basePoint) ≠ Q0 k)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (j : Fin 12) : b65x_shape c w s ≠ Q0 j := by
  by_cases hjk : j = k
  · subst hjk; exact b65x_shape_avoid h2 h3 s hs
  apply b65x_shape_avoid _ _ s hs
  · intro he
    have hsep := b65x_disc_sep j k hjk
    have t1 := norm_sub_le_norm_sub_add_norm_sub (Q0 j) c (b65b_track 0 k)
    have t2 := norm_sub_le_norm_sub_add_norm_sub (b65b_track 0 j) (Q0 j) (b65b_track 0 k)
    have e1 := norm_sub_rev (b65b_track 0 j) (Q0 j)
    have e3 := hQ j
    linarith
  · intro μ hμ he
    have hw : ‖c + w - b65b_track 0 k‖ ≤ b65b_radius k := by
      have := norm_add_le (c - b65b_track 0 k) w
      rw [show c - b65b_track 0 k + w = c + w - b65b_track 0 k by ring] at this
      linarith
    have hcr := b65x_cross_seg (c + w) μ (Complex.ofReal_im μ)
    rw [he] at hcr
    exact b65x_cone_robust k j (Ne.symm hjk) _ _ hw (hQ j).le hcr

theorem b65x_seg_im (w : ℂ) (μ : ℝ) :
    (mr_basePoint + (μ : ℂ) * (w - mr_basePoint)).im = 10 + μ * (w.im - 10) := by
  simp [mr_basePoint, mr_centre]

/-- Static homotopy at a configuration with one point in each open disc: the certified lasso of a
column deforms to a small radial lasso about the point of its disc. -/
theorem b65x_static_start (col : Fin 13) (hc : col.val ≠ 0) (Q0 : Fin 12 → ℂ)
    (hQ : ∀ j, ‖Q0 j - b65b_track 0 j‖ < b65b_radius j) (ρ : ℝ) (hρ : 0 < ρ)
    (hρs : ρ * ‖mr_basePoint - Q0 (b65x_colDisc col hc)‖ ≤
      ((b65b_radius (b65x_colDisc col hc) : ℝ) -
        ‖Q0 (b65x_colDisc col hc) - b65b_track 0 (b65x_colDisc col hc)‖) / 2) :
    ∃ F : unitInterval × unitInterval → ℂ, Continuous F ∧
      (∀ s, F (0, s) = b65b_lasso col s) ∧
      (∀ s, F (1, s) = b65x_shape (Q0 (b65x_colDisc col hc))
        ((ρ : ℂ) * (mr_basePoint - Q0 (b65x_colDisc col hc))) s) ∧
      (∀ t, F (t, 0) = mr_basePoint ∧ F (t, 1) = mr_basePoint) ∧
      ∀ t s j, F (t, s) ≠ Q0 j := by
  set k := b65x_colDisc col hc
  set q := Q0 k
  set ck := b65b_track 0 k
  set r : ℝ := (b65b_radius k : ℝ)
  set d := ‖q - ck‖
  set ρ' := (r - d) / 2
  have hd : d < r := hQ k
  have hρ'def : ρ' = (r - d) / 2 := rfl
  have hrdef : ((b65b_radius k : ℚ) : ℝ) = r := rfl
  have hd0 : 0 ≤ d := norm_nonneg _
  have hρ' : 0 < ρ' := by rw [hρ'def]; linarith
  have hck : ck.im + r < 10 := by
    have := (b65x_outer_rat k).2.1
    have h' : ((b65b_vertex0 k).2 : ℝ) + b65b_radius k < 10 := by exact_mod_cast this
    simpa [ck, b65x_track0] using h'
  have hqim : q.im < 10 := by
    have := Complex.abs_im_le_norm (q - ck)
    have h2 := le_abs_self (q - ck).im
    simp only [Complex.sub_im] at this h2
    linarith
  let cf : ℝ → ℂ := fun l ↦ if l ≤ 1/2 then ck + ((2 * l : ℝ) : ℂ) * (q - ck) else q
  let wf : ℝ → ℂ := fun l ↦ if l ≤ 1/2 then I * (((1 - 2 * l) * r + 2 * l * ρ' : ℝ) : ℂ)
    else ((2 - 2 * l : ℝ) : ℂ) * (I * (ρ' : ℂ)) +
      ((2 * l - 1 : ℝ) : ℂ) * ((ρ : ℂ) * (mr_basePoint - q))
  have hcf : Continuous cf := by
    refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const ?_
    intro l hl; rw [hl]; push_cast; ring
  have hwf : Continuous wf := by
    refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
    intro l hl; rw [hl]; push_cast; ring
  refine ⟨fun q' ↦ b65x_shape (cf q'.1) (wf q'.1) q'.2, ?_, fun s ↦ ?_, fun s ↦ ?_,
    fun t ↦ ⟨b65x_shape_zero _ _, b65x_shape_one _ _⟩, fun t s j ↦ ?_⟩
  · exact b65x_shape_continuous.comp ((hcf.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      ((hwf.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  · have hc0 : cf 0 = ck := by simp [cf]
    have hw0 : wf 0 = I * (r : ℂ) := by simp [wf]
    change b65x_shape (cf 0) (wf 0) s = _
    rw [hc0, hw0, b65x_lasso_shape col hc]
  · have hc1 : cf 1 = q := by simp only [cf]; norm_num
    have hw1 : wf 1 = (ρ : ℂ) * (mr_basePoint - q) := by simp only [wf]; norm_num
    change b65x_shape (cf 1) (wf 1) s = _
    rw [hc1, hw1]
  · -- avoidance
    obtain ⟨t, ht0, ht1⟩ := t
    have hs : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨s.2.1, s.2.2⟩
    change b65x_shape (cf t) (wf t) s ≠ Q0 j
    by_cases hl : t ≤ 1/2
    · set ν := 2 * t with hν
      have hν0 : 0 ≤ ν := by linarith
      have hν1 : ν ≤ 1 := by linarith
      have hcfe : cf t = ck + (ν : ℂ) * (q - ck) := by simp only [cf, ite_eq_left hl, hν]
      have hwfe : wf t = I * (((1 - ν) * r + ν * ρ' : ℝ) : ℂ) := by
        simp only [wf, ite_eq_left hl, hν]
      have hR : 0 ≤ (1 - ν) * r + ν * ρ' := by
        have : 0 ≤ r := (norm_nonneg _).trans hd.le
        positivity
      have hwn : ‖wf t‖ = (1 - ν) * r + ν * ρ' := by
        rw [hwfe, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hR]
      have hcn : ‖cf t - ck‖ = ν * d := by
        rw [hcfe, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hν0]
      have hqn : ‖q - cf t‖ = (1 - ν) * d := by
        rw [hcfe, show q - (ck + (ν : ℂ) * (q - ck)) = ((1 - ν : ℝ) : ℂ) * (q - ck) by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
      have hlt : ‖q - cf t‖ < ‖wf t‖ := by
        rw [hqn, hwn]
        rcases hν1.lt_or_eq with h' | h'
        · nlinarith [norm_nonneg (q - ck)]
        · rw [h']; simp only [sub_self, zero_mul, one_mul, zero_add]; exact hρ'
      apply b65x_disc_shape_avoid k Q0 hQ _ _ _ hlt.ne _ s hs j
      · rw [hcn, hwn, hrdef, hρ'def]; nlinarith
      · intro μ hμ he
        have him := congrArg Complex.im he
        rw [b65x_seg_im] at him
        have htop : (cf t + wf t).im = (cf t).im + ‖wf t‖ := by
          rw [hwn, hwfe]; simp
        have hqc := Complex.abs_im_le_norm (q - cf t)
        have hqc2 := le_abs_self (q - cf t).im
        simp only [Complex.sub_im] at hqc hqc2
        have h1 : (cf t).im ≤ ck.im + ν * d := by
          have := Complex.abs_im_le_norm (cf t - ck)
          have h2 := le_abs_self (cf t - ck).im
          simp only [Complex.sub_im] at this h2
          linarith [hcn]
        have htop10 : (cf t + wf t).im ≤ 10 := by
          rw [htop, hwn, hρ'def]
          nlinarith [mul_nonneg hν0 (sub_nonneg.mpr hd.le)]
        have hqk : (Q0 k).im = q.im := rfl
        rw [hqk] at him
        nlinarith [mul_nonneg (sub_nonneg.mpr hμ.2) (sub_nonneg.mpr htop10)]
    · push Not at hl
      set ν := 2 * t - 1 with hν
      have hν0 : 0 ≤ ν := by linarith
      have hν1 : ν ≤ 1 := by linarith
      have hcfe : cf t = q := by simp only [cf, ite_eq_right (not_le.mpr hl)]
      have hwfe : wf t = ((1 - ν : ℝ) : ℂ) * (I * (ρ' : ℂ)) +
          (ν : ℂ) * ((ρ : ℂ) * (mr_basePoint - q)) := by
        simp only [wf, ite_eq_right (not_le.mpr hl), hν]; push_cast; ring
      have hwime : (wf t).im = (1 - ν) * ρ' + ν * (ρ * (10 - q.im)) := by
        rw [hwfe]; simp [mr_basePoint, mr_centre]
      have hwim : 0 < (wf t).im := by
        rw [hwime]
        have h1 : 0 ≤ ν * (ρ * (10 - q.im)) :=
          mul_nonneg hν0 (mul_nonneg hρ.le (by linarith))
        rcases hν1.lt_or_eq with h' | h'
        · nlinarith [mul_pos (sub_pos.mpr h') hρ']
        · rw [h']; nlinarith [mul_pos hρ (show 0 < 10 - q.im by linarith)]
      have hn1 : ‖((1 - ν : ℝ) : ℂ) * (I * (ρ' : ℂ))‖ = (1 - ν) * ρ' := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_pos hρ']
      have hn2 : ‖(ν : ℂ) * ((ρ : ℂ) * (mr_basePoint - q))‖ = ν * (ρ * ‖mr_basePoint - q‖) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hν0, abs_of_pos hρ]
      have hwn : ‖wf t‖ ≤ ρ' := by
        rw [hwfe]
        have := norm_add_le (((1 - ν : ℝ) : ℂ) * (I * (ρ' : ℂ)))
          ((ν : ℂ) * ((ρ : ℂ) * (mr_basePoint - q)))
        rw [hn1, hn2] at this
        nlinarith [mul_le_mul_of_nonneg_left hρs hν0]
      have hpos : 0 < ‖wf t‖ := lt_of_lt_of_le hwim (Complex.im_le_norm _)
      apply b65x_disc_shape_avoid k Q0 hQ _ _ _ _ _ s hs j
      · rw [hcfe]; linarith
      · rw [hcfe, sub_self, norm_zero]; exact hpos.ne
      · intro μ hμ he
        have him := congrArg Complex.im he
        rw [b65x_seg_im, hcfe] at him
        have hqk : (Q0 k).im = q.im := rfl
        rw [hqk, Complex.add_im] at him
        nlinarith [mul_nonneg (sub_nonneg.mpr hμ.2) (show 0 ≤ 10 - q.im by linarith),
          mul_nonneg hμ.1 hwim.le, mul_pos (show (0:ℝ) < 1 by norm_num) hwim]

theorem b65x_marks_sep (j k : Fin 12) (h : j ≠ k) : 1 ≤ ‖mr_marks j - mr_marks k‖ := by
  have hre : 1 ≤ |(mr_marks j - mr_marks k).re| := by
    fin_cases j <;> fin_cases k <;>
      first
      | exact absurd rfl h
      | norm_num [mr_marks, mr_base, Fin.append, Fin.addCases]
  exact hre.trans (Complex.abs_re_le_norm _)

theorem b65x_marks_im (j : Fin 12) : (mr_marks j).im = 0 := by
  fin_cases j <;> simp [mr_marks, mr_base, Fin.append, Fin.addCases]

/-- Shapes about a mark with a short upward handle avoid every mark. -/
theorem b65x_mark_shape_avoid (k : Fin 12) (w : ℂ) (hw : ‖w‖ ≤ 1/4) (hwim : 0 < w.im)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (j : Fin 12) : b65x_shape (mr_marks k) w s ≠ mr_marks j := by
  apply b65x_shape_avoid _ _ s hs
  · by_cases hjk : j = k
    · subst hjk; rw [sub_self, norm_zero]
      exact (lt_of_lt_of_le hwim (Complex.im_le_norm _)).ne
    · have := b65x_marks_sep j k hjk; intro he; linarith
  · intro μ hμ he
    have him := congrArg Complex.im he
    rw [b65x_seg_im, Complex.add_im, b65x_marks_im, b65x_marks_im, zero_add] at him
    rcases lt_or_ge μ (1/2) with h' | h'
    · nlinarith [mul_nonneg hμ.1 hwim.le]
    · nlinarith [mul_le_mul_of_nonneg_right h' hwim.le, hμ.2]

/-- Static homotopy at the marks from a small radial lasso to the explicit lasso. -/
theorem b65x_static_end (k : Fin 12) (ρ : ℝ) (hρ : 0 < ρ)
    (hρs : ρ * ‖mr_basePoint - mr_marks k‖ ≤ 1/4) :
    ∃ F : unitInterval × unitInterval → ℂ, Continuous F ∧
      (∀ s, F (0, s) = b65x_shape (mr_marks k) ((ρ : ℂ) * (mr_basePoint - mr_marks k)) s) ∧
      (∀ s, F (1, s) = mr_lasso (mr_marks k) s) ∧
      (∀ t, F (t, 0) = mr_basePoint ∧ F (t, 1) = mr_basePoint) ∧
      ∀ t s j, F (t, s) ≠ mr_marks j := by
  let wf : ℝ → ℂ := fun l ↦ ((1 - l : ℝ) : ℂ) * ((ρ : ℂ) * (mr_basePoint - mr_marks k)) +
    (l : ℂ) * (I / 4)
  have hwf : Continuous wf := by fun_prop
  refine ⟨fun q' ↦ b65x_shape (mr_marks k) (wf q'.1) q'.2, ?_, fun s ↦ ?_, fun s ↦ ?_,
    fun t ↦ ⟨b65x_shape_zero _ _, b65x_shape_one _ _⟩, fun t s j ↦ ?_⟩
  · exact b65x_shape_continuous.comp (continuous_const.prodMk
      ((hwf.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  · simp [wf]
  · simp [wf, b65x_mr_lasso_shape]
  · obtain ⟨t, ht0, ht1⟩ := t
    apply b65x_mark_shape_avoid k _ _ _ s ⟨s.2.1, s.2.2⟩ j
    · calc ‖wf t‖ ≤ ‖((1 - t : ℝ) : ℂ) * ((ρ : ℂ) * (mr_basePoint - mr_marks k))‖ +
            ‖(t : ℂ) * (I / 4)‖ := norm_add_le _ _
        _ = (1 - t) * (ρ * ‖mr_basePoint - mr_marks k‖) + t * (1/4) := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_pos hρ, abs_of_nonneg ht0, norm_div,
            Complex.norm_I]
          norm_num
        _ ≤ (1 - t) * (1/4) + t * (1/4) := by gcongr
        _ = 1/4 := by ring
    · simp [wf, mr_basePoint, mr_centre, b65x_marks_im]
      rcases ht1.lt_or_eq with h' | h'
      · nlinarith
      · rw [h']; norm_num

end HodgeLean.Foundations.Program
