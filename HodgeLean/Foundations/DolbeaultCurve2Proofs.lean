import HodgeLean.Foundations.DolbeaultCurve2Defs
import HodgeLean.Foundations.DolbeaultCurve
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Proof obligations for the Dolbeault stage 2: the `∂̄`-Poincaré lemma on curves -/

noncomputable section
open MeasureTheory CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint
open scoped ContDiff Manifold
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations

theorem spec_locallyIntegrable_inv_aux :
    LocallyIntegrable (fun z : ℂ => z⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by simp)
    (Filter.Eventually.of_forall fun z => ?_) (by fun_prop)
  simp [Real.rpow_neg_one]

/-- The unit vector `e^{iθ}`, written as in `Complex.polarCoord_symm_apply`. -/
private abbrev cpU (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I

private lemma cpU_pi : cpU Real.pi = cpU (-Real.pi) := by simp [cpU]

private lemma hasDerivAt_cpU_mul (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => (r : ℂ) * cpU t) ((r : ℂ) * (Complex.I * cpU θ)) θ := by
  have h1 := (Real.hasDerivAt_cos θ).ofReal_comp
  have h2 := ((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I
  have := (h1.add h2).const_mul (r : ℂ)
  convert this using 1
  simp only [cpU]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma hasDerivAt_mul_cpU (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * cpU θ) (cpU θ) r := by
  simpa using ((hasDerivAt_id r).ofReal_comp).mul_const (cpU θ)

/-- Pointwise algebra: in polar coordinates the Cauchy–Pompeiu integrand is the combination
of the radial and angular derivatives. -/
private lemma polar_integrand_eq (L : ℂ →L[ℝ] ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r • (antiLinearPart L 1 / (-((r : ℂ) * cpU θ))) =
      -(2⁻¹ : ℂ) * (L (cpU θ) + Complex.I * L (Complex.I * cpU θ)) := by
  have hu : cpU θ = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • Complex.I := by
    simp [cpU, Complex.real_smul]
  have hIu : Complex.I * cpU θ = (Real.cos θ : ℝ) • Complex.I + (-Real.sin θ : ℝ) • (1 : ℂ) := by
    simp only [cpU, Complex.real_smul]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hmul : ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) *
      ((Real.cos θ : ℂ) - Real.sin θ * Complex.I) = 1 := by
    linear_combination hc - (Real.sin θ : ℂ) ^ 2 * Complex.I_sq
  have hinv := inv_eq_of_mul_eq_one_right hmul
  have hu0 : (Real.cos θ : ℂ) + Real.sin θ * Complex.I ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have key : ∀ A : ℂ, r • (A / (-((r : ℂ) * ((Real.cos θ : ℂ) + Real.sin θ * Complex.I)))) =
      -(A * ((Real.cos θ : ℂ) - Real.sin θ * Complex.I)) := by
    intro A
    rw [Complex.real_smul, ← hinv]
    field_simp
  rw [show (r : ℂ) * cpU θ = (r : ℂ) * ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) from rfl, key,
    hIu, hu, map_add, map_add, map_smul, map_smul, map_smul, map_smul, antiLinearPart_apply]
  simp only [Complex.real_smul, smul_eq_mul, mul_one]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma norm_cpU (θ : ℝ) : ‖cpU θ‖ = 1 := by
  rw [cpU, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I,
    Complex.norm_exp_ofReal_mul_I]

/-- A radius beyond which the derivative of a compactly supported function vanishes along rays. -/
private lemma exists_fderiv_eq_zero_of_lt {g : ℂ → ℂ} (hc : HasCompactSupport g) (z : ℂ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r θ : ℝ, R < |r| →
      g (z + r * cpU θ) = 0 ∧ fderiv ℝ g (z + r * cpU θ) = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0 + ‖z‖, by positivity, fun r θ hr => ?_⟩
  have hn : max R 0 < ‖z + r * cpU θ‖ := by
    have h1 : ‖(r : ℂ) * cpU θ‖ = |r| := by
      rw [norm_mul, norm_cpU, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := norm_sub_norm_le ((r : ℂ) * cpU θ) (-z)
    rw [sub_neg_eq_add, norm_neg, add_comm] at this
    linarith
  have hout : z + r * cpU θ ∉ tsupport g := fun h => by
    have := hR h
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R 0]
  exact ⟨image_eq_zero_of_notMem_tsupport hout,
    by_contra fun h => hout (support_fderiv_subset ℝ h)⟩

private lemma integral_radial {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (z : ℂ)
    (θ : ℝ) : ∫ r in Set.Ioi (0 : ℝ), fderiv ℝ g (z + r * cpU θ) (cpU θ) = -g z := by
  obtain ⟨R, hR0, hR⟩ := exists_fderiv_eq_zero_of_lt hc z
  have hd : ∀ r : ℝ, HasDerivAt (fun s : ℝ => g (z + s * cpU θ))
      (fderiv ℝ g (z + r * cpU θ) (cpU θ)) r := fun r => by
    have := ((hg.differentiable one_ne_zero) (z + r * cpU θ)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_mul_cpU r θ).const_add z)
    exact this
  have hcont : Continuous fun r : ℝ => fderiv ℝ g (z + r * cpU θ) (cpU θ) :=
    ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_const
  have hint : Integrable fun r : ℝ => fderiv ℝ g (z + r * cpU θ) (cpU θ) := by
    refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
      (isCompact_closedBall (0 : ℝ) R) fun r hr => ?_)
    rw [Metric.mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hr
    rw [(hR r θ hr).2]; rfl
  have hlim : Filter.Tendsto (fun s : ℝ => g (z + s * cpU θ)) Filter.atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop R] with r hr
    exact ((hR r θ (by rwa [abs_of_pos (hR0.trans_lt hr)])).1).symm
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd 0).continuousAt.continuousWithinAt
    (fun r _ => hd r) hint.integrableOn hlim]
  simp

private lemma integral_angular {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (z : ℂ) {r : ℝ} (hr : r ≠ 0) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, fderiv ℝ g (z + r * cpU θ) (Complex.I * cpU θ) = 0 := by
  have hd : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => g (z + r * cpU t))
      (r • fderiv ℝ g (z + r * cpU θ) (Complex.I * cpU θ)) θ := fun θ => by
    have := ((hg.differentiable one_ne_zero) (z + r * cpU θ)).hasFDerivAt.comp_hasDerivAt θ
      ((hasDerivAt_cpU_mul r θ).const_add z)
    rw [← map_smul, Complex.real_smul]
    exact this
  have hcont : Continuous fun θ : ℝ => r • fderiv ℝ g (z + r * cpU θ) (Complex.I * cpU θ) :=
    (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (by fun_prop)).const_smul r
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hcont.intervalIntegrable (-Real.pi) Real.pi)
  rw [cpU_pi, sub_self, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, integral_smul, smul_eq_zero] at this
  exact this.resolve_left hr

private lemma integrableOn_polar {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (z : ℂ) {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ g (z + p.1 * cpU p.2) (v p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  obtain ⟨R, -, hR⟩ := exists_fderiv_eq_zero_of_lt hc z
  have hcont : Continuous fun p : ℝ × ℝ => fderiv ℝ g (z + p.1 * cpU p.2) (v p.2) :=
    ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (hv.comp continuous_snd)
  refine IntegrableOn.of_forall_sdiff_eq_zero
    (hcont.continuousOn.integrableOn_compact ((isCompact_Icc (a := (0 : ℝ)) (b := R)).prod
      (isCompact_Icc (a := -Real.pi) (b := Real.pi))))
    (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  have h1' : (0 : ℝ) < p.1 := h1
  have hpR : R < |p.1| := by
    rw [abs_of_pos h1']
    by_contra hle
    exact h3 ⟨⟨h1'.le, not_lt.1 hle⟩, h2.1.le, h2.2.le⟩
  simp [(hR p.1 p.2 hpR).2]

theorem spec_integral_wirtingerDbar_div_aux {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (z : ℂ) :
    ∫ w, wirtingerDbar g w / (z - w) = Real.pi * g z := by
  set F1 : ℝ × ℝ → ℂ := fun p => fderiv ℝ g (z + p.1 * cpU p.2) (cpU p.2) with hF1
  set F2 : ℝ × ℝ → ℂ := fun p => fderiv ℝ g (z + p.1 * cpU p.2) (Complex.I * cpU p.2) with hF2
  have i1 : IntegrableOn F1 (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    integrableOn_polar hg hc z (v := cpU) (by fun_prop)
  have i2 : IntegrableOn F2 (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    integrableOn_polar hg hc z (v := fun θ => Complex.I * cpU θ) (by fun_prop)
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) =
      (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have e1 : ∫ p in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi, F1 p = -(2 * Real.pi * g z) := by
    rw [IntegrableOn, hprod] at i1
    rw [hprod]
    rw [integral_prod_symm _ i1]
    simp only [hF1, integral_radial hg hc z, integral_const]
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
      Complex.real_smul]
    push_cast
    ring
  have e2 : ∫ p in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi, F2 p = 0 := by
    rw [IntegrableOn, hprod] at i2
    rw [hprod]
    rw [integral_prod _ i2]
    refine (setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_).trans (integral_zero _ _)
    exact integral_angular hg z (ne_of_gt hr)
  rw [← integral_add_left_eq_self (fun w => wirtingerDbar g w / (z - w)) z,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    (g := fun p => -(2⁻¹ : ℂ) * (F1 p + Complex.I * F2 p)) fun p hp => ?_]
  · rw [integral_const_mul, integral_add i1 (i2.const_mul _), integral_const_mul, e1, e2]
    ring
  · have hp1 : (0 : ℝ) < p.1 := hp.1
    simp only [Complex.polarCoord_symm_apply, sub_add_cancel_left, wirtingerDbar]
    exact polar_integrand_eq _ hp1 p.2


lemma cauchyTransform_eq_convolution (g : ℂ → ℂ) :
    cauchyTransform g = fun z => (Real.pi : ℂ)⁻¹ *
      convolution g (fun w : ℂ => w⁻¹) (ContinuousLinearMap.mul ℝ ℂ) volume z := by
  ext z
  simp [cauchyTransform, convolution_def, div_eq_mul_inv]

theorem spec_contDiff_cauchyTransform_aux {n : ℕ∞} {g : ℂ → ℂ} (hg : ContDiff ℝ n g)
    (hc : HasCompactSupport g) :
    ContDiff ℝ n (cauchyTransform g) := by
  rw [cauchyTransform_eq_convolution]
  exact contDiff_const.mul (hc.contDiff_convolution_left _ hg spec_locallyIntegrable_inv_aux)

theorem spec_wirtingerDbar_cauchyTransform_aux {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (z : ℂ) :
    wirtingerDbar (cauchyTransform g) z = g z := by
  have hD := (hc.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hg
    spec_locallyIntegrable_inv_aux z).const_mul ((Real.pi : ℂ)⁻¹)
  rw [cauchyTransform_eq_convolution, wirtingerDbar, hD.fderiv]
  have hI : Integrable (fun t => ((ContinuousLinearMap.mul ℝ ℂ).precompL ℂ) (fderiv ℝ g t)
      (z - t)⁻¹) volume :=
    (hc.fderiv ℝ).convolutionExists_left _ (hg.continuous_fderiv one_ne_zero)
      spec_locallyIntegrable_inv_aux z
  have hv : ∀ v : ℂ, (convolution (fderiv ℝ g) (fun z => z⁻¹)
      (ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.mul ℝ ℂ)) volume z) v =
      ∫ t, fderiv ℝ g t v * (z - t)⁻¹ := by
    intro v
    rw [convolution_def, ContinuousLinearMap.integral_apply hI]
    rfl
  have hv' : ∀ v : ℂ, Integrable (fun t => fderiv ℝ g t v * (z - t)⁻¹) volume := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).integrable_comp hI
  have key : ∫ t, wirtingerDbar g t / (z - t) = (2⁻¹ : ℂ) * ((∫ t, fderiv ℝ g t 1 * (z - t)⁻¹)
      + Complex.I * ∫ t, fderiv ℝ g t (Complex.I • 1) * (z - t)⁻¹) := by
    rw [← integral_const_mul, ← integral_add (hv' 1) ((hv' _).const_mul _), ← integral_const_mul]
    congr 1
    ext t
    simp only [wirtingerDbar, antiLinearPart_apply, Complex.real_smul, div_eq_mul_inv]
    push_cast
    ring
  rw [spec_integral_wirtingerDbar_div_aux hg hc z] at key
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : g z = (Real.pi : ℂ)⁻¹ * (Real.pi * g z) := by field_simp
  rw [this, key, antiLinearPart_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hv, Complex.real_smul]
  push_cast
  ring

theorem spec_wirtingerDbar_conj_aux (z : ℂ) :
    wirtingerDbar (starRingEnd ℂ) z = 1 := by
  have : fderiv ℝ (starRingEnd ℂ) z = Complex.conjCLE.toContinuousLinearMap :=
    Complex.conjCLE.fderiv
  rw [wirtingerDbar, this, antiLinearPart_apply]
  simp
  norm_num

theorem spec_cauchyTransform_one_aux (z : ℂ) :
    cauchyTransform (fun _ => 1) z = 0 := by
  rw [cauchyTransform, integral_undef, mul_zero]
  intro h
  have h2 : Integrable (fun w : ℂ => ‖w‖⁻¹) volume := by
    refine (h.comp_sub_left z).norm.congr (Filter.Eventually.of_forall fun w => ?_)
    simp
  have h3 := (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => y⁻¹)).1 h2
  have h4 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := by
    refine h3.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have : (0 : ℝ) < y := hy
    simp [this.ne']
  rw [integrableOn_const_iff] at h4
  simp at h4

/-- `antiLinearPart` commutes with precomposition by a complex-linear map. -/
lemma antiLinearPart_comp_clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E' →L[ℝ] ℂ) (T : E →L[ℂ] E') :
    antiLinearPart (L ∘L T.restrictScalars ℝ) = antiLinearPart L ∘L T.restrictScalars ℝ := by
  ext v
  simp [antiLinearPart_apply, map_smul]

/-- A conjugate-linear functional takes `c • v` to `conj c * L v`. -/
lemma apply_smul_of_antiLinearPart_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L : E →L[ℝ] ℂ} (hL : antiLinearPart L = L) (c : ℂ) (v : E) :
    L (c • v) = starRingEnd ℂ c * L v := by
  have hI : L (Complex.I • v) = -(Complex.I * L v) := by
    rw [← hL, antiLinearPart_apply_I_smul]
  have hc : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
    nth_rw 1 [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hc, map_add, map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- A conjugate-linear functional on `ℂ^1` is `v ↦ conj (v 0) * L 1`. -/
lemma apply_eq_of_antiLinearPart_eq {L : (Fin 1 → ℂ) →L[ℝ] ℂ} (hL : antiLinearPart L = L)
    (v : Fin 1 → ℂ) : L v = starRingEnd ℂ (v 0) * L (fun _ => 1) := by
  have : v = v 0 • (fun _ => (1 : ℂ)) := by
    funext i; fin_cases i; simp
  conv_lhs => rw [this]
  exact apply_smul_of_antiLinearPart_eq hL _ _

/-- Tangent coordinate changes are smooth functions of the base point. -/
lemma contMDiffAt_tangentCoordChange {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {x y z : M}
    (hz : z ∈ (chartAt E x).source ∩ (chartAt E y).source) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞ (tangentCoordChange 𝓘(ℝ, E) x y) z := by
  have : IsManifold 𝓘(ℝ, E) (∞ + 1) M := inferInstanceAs (IsManifold 𝓘(ℝ, E) ∞ M)
  have h : (tangentBundleCore 𝓘(ℝ, E) M).IsContMDiff 𝓘(ℝ, E) ∞ := tangentBundleCore.isContMDiff
  have := (tangentBundleCore 𝓘(ℝ, E) M).contMDiffOn_coordChange (n := ∞) 𝓘(ℝ, E)
    (achart E x) (achart E y)
  exact this.contMDiffAt (((chartAt E x).open_source.inter (chartAt E y).open_source).mem_nhds hz)
/-- A smooth `(0,1)`-form at every point of an open set is smooth there in the tangent coordinates
of one fixed chart. -/
lemma isZeroOneFormAt_chart {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    {σ : ComplexPoint X → (Fin d → ℂ) →L[ℝ] ℂ} {x y : ComplexPoint X}
    (hσ : IsZeroOneFormAt X d σ y) (hy : y ∈ (chartAt (Fin d → ℂ) x).source) :
    ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, (Fin d → ℂ) →L[ℝ] ℂ) ∞
      (fun z => σ z ∘L tangentCoordChange 𝓘(ℝ, Fin d → ℂ) x z z) y := by
  have h1 := hσ.2.clm_comp (contMDiffAt_tangentCoordChange (x := x) (y := y) (z := y)
    ⟨hy, mem_chart_source _ y⟩)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [((chartAt (Fin d → ℂ) x).open_source.inter
    (chartAt (Fin d → ℂ) y).open_source).mem_nhds ⟨hy, mem_chart_source _ y⟩] with z hz
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  rw [tangentCoordChange_comp]
  simp only [extChartAt_source]
  exact ⟨hz, mem_chart_source _ z⟩

theorem spec_exists_dbarSection_eq_aux (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    {U : Opens (ComplexPoint X)} (σ : zeroOneFormSubgroup X 1 U) (x : U) :
    ∃ (V : Opens (ComplexPoint X)) (i : V ≤ U), (x : ComplexPoint X) ∈ V ∧
      ∃ f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), V; 𝓘(ℝ, ℂ), ℂ⟯,
        ∀ y : V, dbarSection X 1 f y = (σ : ∀ _ : U, (Fin 1 → ℂ) →L[ℝ] ℂ) ⟨y, i y.2⟩ := by
  obtain ⟨x, hxU⟩ := x
  let τ := extendSection (σ : ∀ _ : U, (Fin 1 → ℂ) →L[ℝ] ℂ)
  have hσ : ∀ y : U, IsZeroOneFormAt X 1 τ y := σ.2
  let e := chartAt (Fin 1 → ℂ) x
  let W : Set (ComplexPoint X) := (U : Set (ComplexPoint X)) ∩ e.source
  have hWo : IsOpen W := U.isOpen.inter e.open_source
  have hxW : x ∈ W := ⟨hxU, mem_chart_source _ _⟩
  let ρ : ComplexPoint X → (Fin 1 → ℂ) →L[ℝ] ℂ :=
    fun z => τ z ∘L tangentCoordChange 𝓘(ℝ, Fin 1 → ℂ) x z z
  have hρs : ContMDiffOn 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, (Fin 1 → ℂ) →L[ℝ] ℂ) ∞ ρ W := fun y hy =>
    (isZeroOneFormAt_chart (hσ ⟨y, hy.1⟩) hy.2).contMDiffWithinAt
  have hρa : ∀ y ∈ W, antiLinearPart (ρ y) = ρ y := by
    intro y hy
    change antiLinearPart (τ y ∘L _) = τ y ∘L _
    rw [realTangentCoordChange_eq_restrictScalars X 1 x y y hy.2 (mem_localChart_source X 1 y),
      antiLinearPart_comp_restrictScalars, (hσ ⟨y, hy.1⟩).1]
  let R : (Fin 1 → ℂ) → (Fin 1 → ℂ) →L[ℝ] ℂ := fun p => ρ (e.symm p)
  let O : Set (Fin 1 → ℂ) := e.target ∩ e.symm ⁻¹' W
  have hOo : IsOpen O := e.isOpen_inter_preimage_symm hWo
  have hRs : ContDiffOn ℝ ∞ R O := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hρs.comp (contMDiffOn_chart_symm.mono Set.inter_subset_left) (fun p hp => hp.2)
  let ι : ℂ →L[ℝ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℂ
  let x0 : ℂ := e x 0
  have hιx : ι x0 = e x := by funext i; fin_cases i; rfl
  have hO' : ι ⁻¹' O ∈ nhds x0 := by
    refine (hOo.preimage ι.continuous).mem_nhds ?_
    rw [Set.mem_preimage, hιx]
    exact ⟨e.map_source (mem_chart_source _ _), by simpa [e.left_inv (mem_chart_source _ _)]⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.1 hO'
  let χ : ContDiffBump x0 := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let g : ℂ → ℂ := fun w => χ w * R (ι w) (fun _ => 1)
  have hgs : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ Metric.ball x0 ε
    · have hR' : ContDiffAt ℝ ∞ (fun w => R (ι w)) w :=
        (hRs.contDiffAt (hOo.mem_nhds (hεO hw))).comp w ι.contDiff.contDiffAt
      exact ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt).mul
        (hR'.clm_apply contDiffAt_const)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have : w ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        intro h
        exact hw (Metric.closedBall_subset_ball (by change ε / 2 < ε; linarith) h)
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 this] with v hv
      change (χ v : ℂ) * _ = 0
      rw [show χ v = 0 from hv]
      simp
  have hgc : HasCompactSupport g :=
    χ.hasCompactSupport.mono fun w hw =>
      Complex.ofReal_ne_zero.1 (left_ne_zero_of_mul (Function.mem_support.1 hw))
  let T := cauchyTransform g
  have hTs : ContDiff ℝ ∞ T := spec_contDiff_cauchyTransform_aux (n := ⊤) hgs hgc
  have hTd : ∀ z, wirtingerDbar T z = g z := spec_wirtingerDbar_cauchyTransform_aux
    (hgs.of_le (by simp)) hgc
  let F : (Fin 1 → ℂ) → ℂ := fun p => T (p 0)
  have hFs : ContDiff ℝ ∞ F := hTs.comp (contDiff_apply ℝ ℂ (0 : Fin 1))
  let V : Set (ComplexPoint X) := W ∩ e ⁻¹' ((fun p => p 0) ⁻¹' Metric.ball x0 (ε / 4))
  have hVo : IsOpen V := by
    have := e.isOpen_inter_preimage
      ((Metric.isOpen_ball (x := x0) (ε := ε / 4)).preimage (continuous_apply 0))
    simpa only [V, W, Set.inter_assoc] using U.isOpen.inter this
  have hxV : x ∈ V := ⟨hxW, by simp [x0, hε]⟩
  refine ⟨⟨V, hVo⟩, fun y hy => hy.1.1, hxV, ⟨fun y => F (e y), ?_⟩, ?_⟩
  · intro y
    refine contMDiffAt_subtype_iff (f := fun z => F (e z)) |>.2 ?_
    exact hFs.contMDiff.contMDiffAt.comp _
      ((contMDiffOn_chart (I := 𝓘(ℝ, Fin 1 → ℂ)) (n := ∞) (x := x)).contMDiffAt
        (e.open_source.mem_nhds y.2.1.2))
  · rintro ⟨y, hyV⟩
    have hyW : y ∈ W := hyV.1
    have hye : y ∈ e.source := hyW.2
    have hτy : (σ : ∀ _ : U, (Fin 1 → ℂ) →L[ℝ] ℂ) ⟨y, hyW.1⟩ = τ y :=
      (extendSection_of_mem _ hyW.1).symm
    rw [hτy]
    let π : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
    have h1 : extendSection (fun z : (⟨V, hVo⟩ : Opens (ComplexPoint X)) => F (e z)) =ᶠ[nhds y]
        F ∘ e := by
      filter_upwards [hVo.mem_nhds hyV] with z hz
      exact extendSection_of_mem _ hz
    have hFd : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, ℂ) F (e y) :=
      hFs.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hed : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) e y :=
      ((contMDiffOn_chart (I := 𝓘(ℝ, Fin 1 → ℂ)) (n := ∞) (x := x)).contMDiffAt
        (e.open_source.mem_nhds hye)).mdifferentiableAt (by simp)
    have h2 : realDifferential X 1 (extendSection
        (fun z : (⟨V, hVo⟩ : Opens (ComplexPoint X)) => F (e z))) y =
        fderiv ℝ F (e y) ∘L tangentCoordChange 𝓘(ℝ, Fin 1 → ℂ) y x y := by
      rw [realDifferential_congr h1]
      unfold realDifferential
      rw [mfderiv_comp y hFd hed, mfderiv_eq_fderiv, mfderiv_chartAt_eq_tangentCoordChange hye]
      rfl
    have h3 : fderiv ℝ F (e y) = fderiv ℝ T (e y 0) ∘L π.restrictScalars ℝ := by
      have : F = T ∘ (π.restrictScalars ℝ) := rfl
      rw [this, fderiv_comp _ (hTs.differentiable (by simp) _)
        (π.restrictScalars ℝ).differentiableAt, ContinuousLinearMap.fderiv]
      rfl
    have hA : antiLinearPart (fderiv ℝ T (e y 0)) ∘L π.restrictScalars ℝ = R (e y) := by
      have hR1 : antiLinearPart (R (e y)) = R (e y) := by
        change antiLinearPart (ρ (e.symm (e y))) = ρ (e.symm (e y))
        rw [e.left_inv hye]
        exact hρa y hyW
      have hz : e y 0 ∈ Metric.closedBall x0 χ.rIn :=
        Metric.ball_subset_closedBall hyV.2
      have hιy : ι (e y 0) = e y := by funext i; fin_cases i; rfl
      ext w
      rw [apply_eq_of_antiLinearPart_eq hR1 w, ContinuousLinearMap.comp_apply]
      change antiLinearPart (fderiv ℝ T (e y 0)) (w 0) = _
      have : w 0 = w 0 • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
      conv_lhs => rw [this, apply_smul_of_antiLinearPart_eq (antiLinearPart_antiLinearPart _)]
      congr 1
      change wirtingerDbar T (e y 0) = _
      rw [hTd]
      change (χ (e y 0) : ℂ) * R (ι (e y 0)) (fun _ => 1) = _
      rw [χ.one_of_mem_closedBall hz, hιy, Complex.ofReal_one, one_mul]
    unfold dbarSection
    change antiLinearPart (realDifferential X 1 (extendSection
        (fun z : (⟨V, hVo⟩ : Opens (ComplexPoint X)) => F (e z))) y) = τ y
    rw [h2, realTangentCoordChange_eq_restrictScalars X 1 y x y (mem_localChart_source X 1 y) hye,
      antiLinearPart_comp_restrictScalars, ← realTangentCoordChange_eq_restrictScalars X 1 y x y
        (mem_localChart_source X 1 y) hye, h3, antiLinearPart_comp_clm, hA]
    ext v
    change ρ (e.symm (e y)) (tangentCoordChange 𝓘(ℝ, Fin 1 → ℂ) y x y v) = τ y v
    rw [e.left_inv hye]
    change τ y (tangentCoordChange 𝓘(ℝ, Fin 1 → ℂ) x y y
      (tangentCoordChange 𝓘(ℝ, Fin 1 → ℂ) y x y v)) = τ y v
    rw [tangentCoordChange_comp, tangentCoordChange_self]
    · simp only [extChartAt_source]; exact mem_chart_source _ y
    · simp only [extChartAt_source]; exact ⟨⟨mem_chart_source _ y, hye⟩, mem_chart_source _ y⟩

theorem spec_epi_dbar_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (hd : d = 1) :
    Epi (dbar X d) := by
  subst hd
  have h : TopCat.Presheaf.IsLocallySurjective (dbar X 1).hom := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U σ x hx
    obtain ⟨V, i, hxV, f, hf⟩ := spec_exists_dbarSection_eq_aux X σ ⟨x, hx⟩
    exact ⟨V, i, ⟨f, Subtype.ext (funext hf)⟩, hxV⟩
  have : Sheaf.IsLocallySurjective (dbar X 1) := h
  exact Sheaf.epi_of_isLocallySurjective _

lemma antiLinearPart_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (L : E →L[ℝ] ℂ) : antiLinearPart (c • L) = c • antiLinearPart L := by
  ext v
  simp only [antiLinearPart_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem spec_isZeroOneFormAt_smul_aux {X : Over (Spec ↧ℂ)} {d : ℕ}
    [SmoothOfRelativeDimension d X.hom] {f : ComplexPoint X → ℂ}
    {σ : ComplexPoint X → (Fin d → ℂ) →L[ℝ] ℂ} {x : ComplexPoint X}
    (hf : ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ f x) (hσ : IsZeroOneFormAt X d σ x) :
    IsZeroOneFormAt X d (fun y => f y • σ y) x := by
  refine ⟨by rw [antiLinearPart_smul, hσ.1], ?_⟩
  have := (ContinuousLinearMap.lsmul ℝ ℂ :
      ℂ →L[ℝ] ((Fin d → ℂ) →L[ℝ] ℂ) →L[ℝ] ((Fin d → ℂ) →L[ℝ] ℂ)).isBoundedBilinearMap.contDiff
    |>.comp_contMDiffAt (hf.prodMk_space hσ.2)
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.smul_comp]

theorem spec_subsingleton_hypercohomology_two_of_acyclic_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (hd : dim X.left = 1)
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) :=
  spec_subsingleton_hypercohomology_two_of_dbar X hd (spec_epi_dbar_aux X _ hd) hA hB

theorem spec_cycleClassIsHodge_of_curve_of_acyclic_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_of_dbar X
    (spec_epi_dbar_aux X _ (SmoothOfRelativeDimension.dim_eq X.hom 1)) hA hB

end HodgeLean.Foundations
