import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cIntersection

noncomputable section

namespace HodgeLean.Foundations.Program

theorem b6m_orient_complex_coordinates :
    ∃ κ : ℝ, 0 < κ ∧ ∀ v w : ℂ,
      b3_orient ℂ v w = κ * (v.re * w.im - v.im * w.re) := by
  let f := (Module.finBasis ℂ ℂ).equivFun
  have hf : ∀ z : ℂ, f z = z • f 1 := fun z ↦ by
    simpa only [smul_eq_mul, mul_one] using f.map_smul z 1
  refine ⟨∑ i, Complex.normSq (f 1 i), ?_, fun v w ↦ ?_⟩
  · have hne : f 1 ≠ 0 := fun h ↦ one_ne_zero (f.injective (h.trans f.map_zero.symm))
    obtain ⟨i, hi⟩ : ∃ i, f 1 i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
      (Finset.single_le_sum (fun j _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ i))
  · change (∑ i, (starRingEnd ℂ (f v i) * f w i).im) = _
    rw [hf v, hf w, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    have h : starRingEnd ℂ v * starRingEnd ℂ (f 1 i) * (w * f 1 i) =
        (Complex.normSq (f 1 i) : ℂ) * (starRingEnd ℂ v * w) := by
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [h, Complex.im_ofReal_mul]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

theorem b6m_orient_rankOne (φ : ℂ →ₗ[ℝ] ℝ) (a v w : ℂ) :
    b3_orient ℂ (v + φ v • a) (w + φ w • a) =
      (1 + φ a) * b3_orient ℂ v w := by
  obtain ⟨κ, _, hκ⟩ := b6m_orient_complex_coordinates
  have hφ : ∀ z : ℂ, φ z = z.re * φ 1 + z.im * φ Complex.I := by
    intro z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    conv_lhs => rw [hz, map_add, map_smul, map_smul]
    rfl
  rw [hκ, hκ, hφ a, hφ v, hφ w]
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add]
  ring

theorem b6m_orient_sign_rankOne (φ : ℂ →L[ℝ] ℝ) (a : ℂ)
    (ha : ‖φ‖ * ‖a‖ < 1) (v w : ℂ) :
    SignType.sign (b3_orient ℂ (v + φ v • a) (w + φ w • a)) =
      SignType.sign (b3_orient ℂ v w) := by
  have hn : ‖φ a‖ < 1 := (φ.le_opNorm a).trans_lt ha
  have hp : 0 < 1 + φ a := by
    have h := neg_le_abs (φ a)
    rw [Real.norm_eq_abs] at hn
    linarith
  have h := b6m_orient_rankOne φ.toLinearMap a v w
  change b3_orient ℂ (v + φ v • a) (w + φ w • a) =
    (1 + φ a) * b3_orient ℂ v w at h
  rw [h, sign_mul, sign_pos hp, one_mul]

theorem b6m_orient_sign_scalar_shift (ρ : ℂ → ℝ) (K : NNReal)
    (hρ : LipschitzWith K ρ) (z a : ℂ) (hd : DifferentiableAt ℝ ρ z)
    (ha : (K : ℝ) * ‖a‖ < 1) (v w : ℂ) :
    SignType.sign (b3_orient ℂ
      (fderiv ℝ (fun x : ℂ ↦ x + ρ x • a) z v)
      (fderiv ℝ (fun x : ℂ ↦ x + ρ x • a) z w)) =
      SignType.sign (b3_orient ℂ v w) := by
  have hf : fderiv ℝ (fun x : ℂ ↦ x + ρ x • a) z =
      ContinuousLinearMap.id ℝ ℂ + (fderiv ℝ ρ z).smulRight a :=
    ((hasFDerivAt_id z).add (hd.hasFDerivAt.smul_const a)).fderiv
  rw [hf]
  change SignType.sign (b3_orient ℂ
    (v + fderiv ℝ ρ z v • a) (w + fderiv ℝ ρ z w • a)) = _
  apply b6m_orient_sign_rankOne
  exact (mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lipschitz ℝ hρ) (norm_nonneg a)).trans_lt ha

theorem b6m_radial_tent_lipschitz (c : ℂ) (r : ℝ) (hr : 0 < r) :
    LipschitzWith ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
      (fun z : ℂ ↦ max 0 (1 - dist z c / r)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (max 0 (1 - dist x c / r)) (max 0 (1 - dist y c / r)) ≤
    r⁻¹ * dist x y
  rw [Real.dist_eq]
  calc
    |max 0 (1 - dist x c / r) - max 0 (1 - dist y c / r)| ≤
        |(1 - dist x c / r) - (1 - dist y c / r)| :=
      (abs_max_sub_max_le_max 0 _ 0 _).trans (by simp)
    _ = |dist y c - dist x c| / r := by
      rw [show (1 - dist x c / r) - (1 - dist y c / r) =
        (dist y c - dist x c) / r by ring, abs_div, abs_of_pos hr]
    _ ≤ dist x y / r := div_le_div_of_nonneg_right
      (by simpa [dist_comm] using abs_dist_sub_le y x c) hr.le
    _ = r⁻¹ * dist x y := by ring

open scoped Topology

theorem b6m_radial_tent_differentiable (c z : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : z ≠ c) (hb : dist z c ≠ r) :
    DifferentiableAt ℝ (fun x : ℂ ↦ max 0 (1 - dist x c / r)) z := by
  let f : ℂ → ℝ := fun x ↦ 1 - dist x c / r
  have hf : Continuous f := continuous_const.sub ((continuous_id.dist continuous_const).div_const r)
  have hd : DifferentiableAt ℝ f z := by
    dsimp [f]
    simp only [dist_eq_norm, div_eq_mul_inv]
    exact (differentiableAt_const (c := (1 : ℝ))).sub
      (((differentiableAt_id.sub_const c).norm ℝ (sub_ne_zero.mpr hc)).mul_const r⁻¹)
  have hn : f z ≠ 0 := by
    dsimp [f]
    intro h
    apply hb
    apply (div_eq_one_iff_eq hr.ne').mp
    linarith
  rcases lt_or_gt_of_ne hn with hn | hn
  · apply (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have he : ∀ᶠ x in 𝓝 z, f x < 0 := (isOpen_lt hf continuous_const).mem_nhds hn
    filter_upwards [he] with x hx
    exact max_eq_left hx.le
  · apply hd.congr_of_eventuallyEq
    have he : ∀ᶠ x in 𝓝 z, 0 < f x := (isOpen_lt continuous_const hf).mem_nhds hn
    filter_upwards [he] with x hx
    exact max_eq_right hx.le

theorem b6m_radial_shift_orientation (c z a : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : z ≠ c) (hb : dist z c ≠ r) (ha : ‖a‖ < r) (v w : ℂ) :
    SignType.sign (b3_orient ℂ
      (fderiv ℝ (fun x : ℂ ↦ x + (max 0 (1 - dist x c / r)) • a) z v)
      (fderiv ℝ (fun x : ℂ ↦ x + (max 0 (1 - dist x c / r)) • a) z w)) =
      SignType.sign (b3_orient ℂ v w) := by
  apply b6m_orient_sign_scalar_shift _ _ (b6m_radial_tent_lipschitz c r hr) z a
    (b6m_radial_tent_differentiable c z r hr hc hb)
  change r⁻¹ * ‖a‖ < 1
  rw [← div_eq_inv_mul]
  exact (div_lt_one hr).mpr ha

end HodgeLean.Foundations.Program
