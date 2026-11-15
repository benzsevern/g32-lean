import HodgeLean.Foundations.Program.BraidBridgesThreeAux
import HodgeLean.Foundations.Program.BraidBridgesThreeTransport

/-! # Transported lasso classes along the certified path

Each slot lasso other than the p10 slot is carried by a small radial lasso to the explicit lasso
of its mark; along the auxiliary path every slot lasso is carried to the explicit lasso of a mark,
which gives the product relation of the slot lassos; the class of the p10 slot then follows from
the product relation of the explicit loops.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex Set
namespace HodgeLean.Foundations.Program

/-- A based loop in a subset of the sphere from a continuous curve inside it. -/
def b65x_mkPath (Y : Set (OnePoint ℂ)) (y : Y) (f : unitInterval → OnePoint ℂ)
    (hf : Continuous f) (hmem : ∀ s, f s ∈ Y) (h0 : f 0 = y) (h1 : f 1 = y) : Path y y where
  toFun s := ⟨f s, hmem s⟩
  continuous_toFun := hf.subtype_mk _
  source' := Subtype.ext h0
  target' := Subtype.ext h1

theorem b65x_outer_norm (s : ℝ) : ‖mr_outer s + 11/2‖ = 10 := by
  simp only [mr_outer, mr_centre]
  rw [show -11 / 2 + 10 * I * cexp (-(2 * Real.pi * I * (s : ℂ))) + 11 / 2 =
    10 * I * cexp (-(2 * Real.pi * I * (s : ℂ))) by ring]
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp]
  simp

theorem b65x_disc_outer (k : Fin 12) (q : ℂ) (hq : ‖q - b65b_track 0 k‖ < b65b_radius k) :
    ‖q + 11/2‖ < 10 := by
  have hout' := (Rat.cast_lt (K := ℝ)).mpr (b65x_outer_rat k).1
  push_cast at hout'
  have hr : (b65b_radius k : ℝ) < 10 := by
    have h' : (b65b_radius k : ℚ) < 10 := by
      have := (b65b_rational_enclosures.1 k).2; linarith
    exact_mod_cast h'
  have hc10 : ‖b65b_track 0 k + 11/2‖ < 10 - b65b_radius k := by
    apply lt_of_pow_lt_pow_left₀ 2 (by linarith)
    rw [b65x_norm_sq, b65x_track0]; simpa using hout'
  have := norm_add_le (q - b65b_track 0 k) (b65b_track 0 k + 11/2)
  rw [show q - b65b_track 0 k + (b65b_track 0 k + 11/2) = q + 11/2 by ring] at this
  linarith

theorem b65x_marks_outer (k : Fin 12) : ‖mr_marks k + 11/2‖ ≤ 13/2 := by
  have hre : |(mr_marks k).re + 11/2| ≤ 13/2 := by
    fin_cases k <;> norm_num [mr_marks, mr_base, Fin.append, Fin.addCases, abs_le]
  have hn : ‖mr_marks k + 11/2‖ = |(mr_marks k).re + 11/2| := by
    have h1 : mr_marks k + 11/2 = (((mr_marks k).re + 11/2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [b65x_marks_im]
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
  rw [hn]; exact hre

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp in
theorem b65x_main_outer (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 12) :
    ‖b65b_configuration p t k + 11/2‖ < 10 := by
  by_cases h : t ≤ 1/2
  · exact b65x_disc_outer k _ (b65x_config_disc p hp t ⟨ht.1, h⟩ k)
  · push Not at h
    have hu : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
    rw [b65b_configuration, ite_eq_right (not_le.mpr h)]
    have := b65b_path_geometry.2.1 _ hu k
    rw [show b65b_track (2 * t - 1) k + 11/2 = b65b_track (2 * t - 1) k - (-11/2 : ℂ) by ring]
    exact this

include hp in
theorem b65x_aux_outer (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) (k : Fin 12) :
    ‖b65x_aux p τ k + 11/2‖ < 10 := by
  by_cases h1 : τ ≤ 1/3
  · simp only [b65x_aux, ite_eq_left h1]
    exact b65x_main_outer p hp _ ⟨by linarith [hτ.1], by linarith⟩ k
  have hX : ‖((b65x_proj k : ℝ) : ℂ) + 11/2‖ < 10 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (b65x_proj_rat k).2
    push_cast at h
    have e : ((b65x_proj k : ℝ) : ℂ) + 11/2 = (((b65x_proj k : ℝ) + 11/2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt_of_sq_lt_sq' h (by norm_num) |>.2 |> fun h2 ↦ by
      rw [abs_lt]; constructor <;> nlinarith
  push Not at h1
  by_cases h2 : τ ≤ 2/3
  · simp only [b65x_aux, ite_eq_right (not_le.mpr h1), ite_eq_left h2]
    have hc : ‖b65b_track 0 k + 11/2‖ < 10 :=
      b65x_disc_outer k _ (by rw [sub_self, norm_zero]; exact_mod_cast (b65x_outer_rat k).2.2)
    set l := 3 * τ - 1
    have hl0 : 0 ≤ l := by simp only [l]; linarith
    have hl1 : l ≤ 1 := by simp only [l]; linarith
    have e : b65b_track 0 k + (l : ℂ) * (((b65x_proj k : ℝ) : ℂ) - b65b_track 0 k) + 11/2 =
        ((1 - l : ℝ) : ℂ) * (b65b_track 0 k + 11/2) + (l : ℂ) * (((b65x_proj k : ℝ) : ℂ) + 11/2) := by
      push_cast; ring
    rw [e]
    calc _ ≤ ‖((1 - l : ℝ) : ℂ) * (b65b_track 0 k + 11/2)‖ +
          ‖(l : ℂ) * (((b65x_proj k : ℝ) : ℂ) + 11/2)‖ := norm_add_le _ _
      _ = (1 - l) * ‖b65b_track 0 k + 11/2‖ + l * ‖((b65x_proj k : ℝ) : ℂ) + 11/2‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg hl0]
      _ < 10 := by
        rcases hl1.lt_or_eq with h' | h'
        · nlinarith [norm_nonneg (((b65x_proj k : ℝ) : ℂ) + 11/2)]
        · rw [h']; simp only [sub_self, zero_mul, one_mul, zero_add]; exact hX
  · push Not at h2
    simp only [b65x_aux, ite_eq_right (not_le.mpr h1), ite_eq_right (not_le.mpr h2)]
    set l := 3 * τ - 2
    have hl0 : 0 ≤ l := by simp only [l]; linarith
    have hl1 : l ≤ 1 := by simp only [l]; linarith [hτ.2]
    have hm := b65x_marks_outer (b65x_auxMark k)
    have e : ((b65x_proj k : ℝ) : ℂ) + (l : ℂ) * (mr_marks (b65x_auxMark k) - ((b65x_proj k : ℝ) : ℂ)) +
        11/2 = ((1 - l : ℝ) : ℂ) * (((b65x_proj k : ℝ) : ℂ) + 11/2) +
          (l : ℂ) * (mr_marks (b65x_auxMark k) + 11/2) := by
      push_cast; ring
    rw [e]
    calc _ ≤ ‖((1 - l : ℝ) : ℂ) * (((b65x_proj k : ℝ) : ℂ) + 11/2)‖ +
          ‖(l : ℂ) * (mr_marks (b65x_auxMark k) + 11/2)‖ := norm_add_le _ _
      _ = (1 - l) * ‖((b65x_proj k : ℝ) : ℂ) + 11/2‖ + l * ‖mr_marks (b65x_auxMark k) + 11/2‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg hl0]
      _ < 10 := by nlinarith [norm_nonneg (((b65x_proj k : ℝ) : ℂ) + 11/2)]

end Witness

theorem b65x_mr_curve_cast (m : Fin 12) (s : ℝ) :
    mr_curve m.castSucc s = ((mr_lasso (mr_marks m) s : ℂ) : OnePoint ℂ) := by
  simp [mr_curve]

/-- The transported lasso of an unblocked column is the explicit lasso of the mark reached by
its point. -/
theorem b65x_radial_class (Q : ℝ → Fin 12 → ℂ) (hQ : Continuous Q)
    (hQ0 : ∀ j, ‖Q 0 j - b65b_track 0 j‖ < b65b_radius j)
    (e : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (heB : e (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ))
    (heI : e OnePoint.infty = OnePoint.infty)
    (heQ : ∀ j, e (Q 0 j : OnePoint ℂ) = (Q 1 j : OnePoint ℂ))
    (hfam : ∀ (K : C(unitInterval × unitInterval, OnePoint ℂ)),
        (∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ)) →
        (∀ t s, K (t, s) ≠ OnePoint.infty ∧ ∀ j, K (t, s) ≠ (Q t j : OnePoint ℂ)) →
        ∀ (Y : Set (OnePoint ℂ)),
          (∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) → w ∈ Y) →
          ∀ {y : Y} (γ γ' : Path y y), (∀ s, (γ s : OnePoint ℂ) = K (1, s)) →
            (∀ s, (γ' s : OnePoint ℂ) = e (K (0, s))) → γ'.Homotopic γ)
    (hQ1 : ∀ i, ∃ j, Q 1 j = mr_marks i)
    (col : Fin 13) (hc : col.val ≠ 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b, b ≠ b65x_colDisc col hc → ∀ μ ∈ Icc (0 : ℝ) 1,
      mr_basePoint + (μ : ℂ) * (Q t (b65x_colDisc col hc) - mr_basePoint) ≠ Q t b)
    (hBk : ∀ t ∈ Icc (0 : ℝ) 1, Q t (b65x_colDisc col hc) ≠ mr_basePoint)
    (m : Fin 12) (hm : Q 1 (b65x_colDisc col hc) = mr_marks m)
    {y : b6t_punctured mr_base} (hy : (y : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ))
    (γ γ' : Path y y) (hγ : ∀ s, (γ s : OnePoint ℂ) = e (b65b_lasso col s : OnePoint ℂ))
    (hγ' : ∀ s, (γ' s : OnePoint ℂ) = mr_curve m.castSucc s) : γ.Homotopic γ' := by
  set k := b65x_colDisc col hc
  have hY : ∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) →
      w ∈ b6t_punctured mr_base := by
    intro w hw hj
    apply b65x_mem_punctured hw
    intro i
    obtain ⟨j, hj'⟩ := hQ1 i
    rw [← hj']; exact hj j
  obtain ⟨ρ0, hρ0, hvalid⟩ := b65x_radial_valid Q hQ k hseg hBk
  set q := Q 0 k
  set d0 := ‖q - b65b_track 0 k‖
  have hd0 : d0 < b65b_radius k := hQ0 k
  set X := ((b65b_radius k : ℝ) - d0) / 2
  have hX : 0 < X := by simp only [X]; linarith
  set N1 := ‖mr_basePoint - q‖
  set N2 := ‖mr_basePoint - mr_marks m‖
  set ρ := min ρ0 (min (X / (N1 + 1)) ((1/4) / (N2 + 1)))
  have hN1 : 0 ≤ N1 := norm_nonneg _
  have hN2 : 0 ≤ N2 := norm_nonneg _
  have hρpos : 0 < ρ := by positivity
  have hρle : ρ ≤ ρ0 := min_le_left _ _
  have hρ1 : ρ * N1 ≤ X := by
    have h : ρ ≤ X / (N1 + 1) := (min_le_right _ _).trans (min_le_left _ _)
    calc ρ * N1 ≤ X / (N1 + 1) * N1 := mul_le_mul_of_nonneg_right h hN1
      _ ≤ X := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have hρ2 : ρ * N2 ≤ 1/4 := by
    have h : ρ ≤ (1/4) / (N2 + 1) := (min_le_right _ _).trans (min_le_right _ _)
    calc ρ * N2 ≤ (1/4) / (N2 + 1) * N2 := mul_le_mul_of_nonneg_right h hN2
      _ ≤ 1/4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have hval := hvalid ρ hρpos hρle
  -- the radial family
  let Rf : unitInterval × unitInterval → ℂ := fun q' ↦
    b65x_shape (Q q'.1 k) ((ρ : ℂ) * (mr_basePoint - Q q'.1 k)) q'.2
  have hRc : Continuous Rf := by
    have hq : Continuous fun q' : unitInterval × unitInterval ↦ Q q'.1 k :=
      ((continuous_apply k).comp hQ).comp (continuous_subtype_val.comp continuous_fst)
    exact b65x_shape_continuous.comp (hq.prodMk
      ((continuous_const.mul (continuous_const.sub hq)).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  let R : C(unitInterval × unitInterval, OnePoint ℂ) :=
    ⟨fun q' ↦ (Rf q' : OnePoint ℂ), OnePoint.continuous_coe.comp hRc⟩
  have hRb : ∀ t, R (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ R (t, 1) = (mr_basePoint : OnePoint ℂ) :=
    fun t ↦ ⟨congrArg _ (b65x_shape_zero _ _), congrArg _ (b65x_shape_one _ _)⟩
  have hRa : ∀ t s, R (t, s) ≠ OnePoint.infty ∧ ∀ j, R (t, s) ≠ (Q t j : OnePoint ℂ) := by
    intro t s
    refine ⟨OnePoint.coe_ne_infty _, fun j h ↦ ?_⟩
    exact hval t t.2 s ⟨s.2.1, s.2.2⟩ j (OnePoint.coe_injective h)
  have he_mem : ∀ w : ℂ, (∀ j, w ≠ Q 0 j) → e (w : OnePoint ℂ) ∈ b6t_punctured mr_base := by
    intro w hw
    apply hY
    · intro h; rw [← heI] at h; exact OnePoint.coe_ne_infty _ (e.injective h)
    · intro j h; rw [← heQ j] at h; exact hw j (OnePoint.coe_injective (e.injective h))
  -- the three paths
  let Pe0 : Path y y := b65x_mkPath _ y (fun s ↦ e (Rf (0, s) : OnePoint ℂ))
    (e.continuous.comp (OnePoint.continuous_coe.comp
      (hRc.comp (continuous_const.prodMk continuous_id))))
    (fun s ↦ he_mem _ fun j h ↦ hval 0 (by simp) s ⟨s.2.1, s.2.2⟩ j h)
    (by simp only [Rf, Set.Icc.coe_zero, b65x_shape_zero]; rw [heB, hy])
    (by simp only [Rf, Set.Icc.coe_one, b65x_shape_one]; rw [heB, hy])
  let P1 : Path y y := b65x_mkPath _ y (fun s ↦ (Rf (1, s) : OnePoint ℂ))
    (OnePoint.continuous_coe.comp (hRc.comp (continuous_const.prodMk continuous_id)))
    (fun s ↦ hY _ (OnePoint.coe_ne_infty _) fun j h ↦
      hval 1 (by simp) s ⟨s.2.1, s.2.2⟩ j (OnePoint.coe_injective h))
    (by simp only [Rf, Set.Icc.coe_zero, b65x_shape_zero]; rw [hy])
    (by simp only [Rf, Set.Icc.coe_one, b65x_shape_one]; rw [hy])
  have h1 : Pe0.Homotopic P1 := hfam R hRb hRa _ hY P1 Pe0 (fun s ↦ rfl) (fun s ↦ rfl)
  -- static homotopy at the start
  obtain ⟨F0, hF0c, hF00, hF01, hF0b, hF0a⟩ :=
    b65x_static_start col hc (Q 0) hQ0 ρ hρpos (by simpa [N1] using hρ1)
  have h0 : γ.Homotopic Pe0 := by
    apply b65x_transport_static (Q 0) (Q 1) e heB heI heQ F0 hF0c hF0b hF0a _ hY hy
    · intro s; rw [hγ, hF00]
    · intro s
      change e (Rf (0, s) : OnePoint ℂ) = e (F0 (1, s) : OnePoint ℂ)
      rw [hF01]; rfl
  -- static homotopy at the end
  obtain ⟨F1, hF1c, hF10, hF11, hF1b, hF1a⟩ := b65x_static_end m ρ hρpos (by simpa [N2] using hρ2)
  have h2 : P1.Homotopic γ' := by
    apply b65x_homotopic_of_family P1 γ' (fun q' ↦ (F1 q' : OnePoint ℂ))
      (OnePoint.continuous_coe.comp hF1c)
    · intro q'
      exact b65x_mem_punctured (OnePoint.coe_ne_infty _) fun i h ↦
        hF1a q'.1 q'.2 i (OnePoint.coe_injective h)
    · intro s
      change (F1 (0, s) : OnePoint ℂ) = (Rf (1, s) : OnePoint ℂ)
      rw [hF10]
      simp only [Rf, Set.Icc.coe_one]
      rw [hm]
    · intro s; rw [hF11, hγ', b65x_mr_curve_cast]
    · intro t; rw [(hF1b t).1, (hF1b t).2, hy]; exact ⟨rfl, rfl⟩
  exact h0.trans (h1.trans h2)

end HodgeLean.Foundations.Program
