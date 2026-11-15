import HodgeLean.Foundations.Program.CurveJacobianRest2ArcDual

/-! # Track B3, lane Rest2: shifted loops and orientations read in a chart

* velocities of shifted paths and of `1`-periodic paths (`b3Rest2_velocity_shift`,
  `b3Rest2_velocity_add_int`), and the invariance of line integrals along loops under shifts of
  the parameter and of the period interval;
* `b3Rest2_sign_orient`: at a common point `γ₁ t = γ₂ s` in the chart at `x`, the sign of the
  orientation of the velocities is the sign of `Im (conj c₁' · c₂')` for the complex chart
  derivatives `cᵢ'`: the change of charts is complex linear, i.e. multiplication by a nonzero
  `μ` on the model line, which multiplies `Im (conj z w)` by `|μ|²`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff ComplexConjugate

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

theorem b3Rest2_contMDiff_shift {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (a : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t ↦ γ (t + a)) :=
  hγ.comp (contDiff_id.add contDiff_const).contMDiff

theorem b3Rest2_velocity_shift {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (a t : ℝ) :
    b3Forms_velocity (E := E) (fun t ↦ γ (t + a)) t = b3Forms_velocity (E := E) γ (t + a) := by
  rw [b3Forms_velocity_eq ((b3Rest2_contMDiff_shift hγ a).mdifferentiableAt one_ne_zero),
    b3Forms_velocity_eq (hγ.mdifferentiableAt one_ne_zero)]
  exact deriv_comp_add_const (chartAt E (γ (t + a)) ∘ γ) a t

theorem b3Rest2_velocity_add_int {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hper : Function.Periodic γ 1) (t : ℝ) (n : ℤ) :
    b3Forms_velocity (E := E) γ (t + n) = b3Forms_velocity (E := E) γ t := by
  have h := b3Rest2_velocity_shift hγ (n : ℝ) t
  have he : (fun t ↦ γ (t + n)) = γ := funext fun t ↦ by
    simpa using (hper.int_mul n) t
  rw [he] at h
  exact h.symm

/-- The integrand of a line integral along a `1`-periodic path is `1`-periodic. -/
theorem b3Rest2_lineIntegrand_periodic (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (hper : Function.Periodic γ 1) :
    Function.Periodic (fun t ↦ α (γ t) (fun _ ↦ b3Forms_velocity γ t)) 1 := by
  intro t
  have h := b3Rest2_velocity_add_int hγ hper t 1
  simp only [Int.cast_one] at h
  simp only [hper t, h]

theorem b3Rest2_lineIntegral_period (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (hper : Function.Periodic γ 1) (s₀ : ℝ) :
    b3Forms_lineIntegral α γ s₀ (s₀ + 1) = b3Forms_lineIntegral α γ 0 1 := by
  have := (b3Rest2_lineIntegrand_periodic α hγ hper).intervalIntegral_add_eq s₀ 0
  rw [zero_add] at this
  exact this

theorem b3Rest2_lineIntegral_shift (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (hper : Function.Periodic γ 1) (a : ℝ) :
    b3Forms_lineIntegral α (fun t ↦ γ (t + a)) 0 1 = b3Forms_lineIntegral α γ 0 1 := by
  unfold b3Forms_lineIntegral
  simp_rw [b3Rest2_velocity_shift hγ a]
  rw [intervalIntegral.integral_comp_add_right (fun t ↦ α (γ t) (fun _ ↦ b3Forms_velocity γ t)),
    zero_add, add_comm 1 a]
  exact b3Rest2_lineIntegral_period α hγ hper a

/-! ## Orientations in a chart -/

/-- On the model line the orientation form is a positive multiple of `Im (conj z w)` in the
coordinate `z ↦ z e`. -/
theorem b3Rest2_orient_L (hE : Module.finrank ℂ E = 1) :
    ∃ κ > 0, ∀ z w : ℂ, b3_orient E (b3Rest_L hE z) (b3Rest_L hE w) = κ * (conj z * w).im := by
  set f := Module.finBasis ℂ E
  set e := b3Rest_e hE
  refine ⟨∑ i, Complex.normSq (f.equivFun e i), ?_, fun z w ↦ ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, f.equivFun e i ≠ 0 := by
      by_contra h
      push_neg at h
      refine b3Rest_e_ne_zero hE ?_
      rw [← f.sum_equivFun (b3Rest_e hE)]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [h i, zero_smul]
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hi)
      (Finset.single_le_sum (fun j _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ i))
  · simp only [b3_orient, b3Rest_L_apply, map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, show starRingEnd ℂ z * starRingEnd ℂ (f.equivFun e i) * (w * f.equivFun e i) =
      (Complex.normSq (f.equivFun e i) : ℂ) * (starRingEnd ℂ z * w) by
        rw [Complex.normSq_eq_conj_mul_self]; ring]
    rw [Complex.im_ofReal_mul]

theorem b3Rest2_sign_normSq_mul {μ : ℂ} (hμ : μ ≠ 0) (z w : ℂ) :
    SignType.sign ((conj (μ * z) * (μ * w)).im) = SignType.sign ((conj z * w).im) := by
  have : (conj (μ * z) * (μ * w)).im = Complex.normSq μ * (conj z * w).im := by
    rw [map_mul, show starRingEnd ℂ μ * starRingEnd ℂ z * (μ * w) =
      (Complex.normSq μ : ℂ) * (starRingEnd ℂ z * w) by
        rw [Complex.normSq_eq_conj_mul_self]; ring, Complex.im_ofReal_mul]
  rw [this, sign_mul, sign_pos (Complex.normSq_pos.2 hμ), one_mul]

theorem b3Rest2_sign_pos_mul {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    SignType.sign (κ * x) = SignType.sign x := by
  rw [sign_mul, sign_pos hκ, one_mul]

/-- A complex-linear endomorphism of the model line is a multiplication in the coordinate
`z ↦ z e`. -/
theorem b3Rest2_line_mul (hE : Module.finrank ℂ E = 1) (T : E →L[ℂ] E) :
    ∃ μ : ℂ, ∀ z : ℂ, (b3Rest_L hE).symm (T (b3Rest_L hE z)) = μ * z := by
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' (b3Rest_e hE) (b3Rest_e_ne_zero hE)).1 hE
    (T (b3Rest_e hE))
  refine ⟨μ, fun z ↦ ?_⟩
  rw [b3Rest_L_apply, map_smul, ← hμ, smul_smul, ← b3Rest_L_apply,
    ContinuousLinearEquiv.symm_apply_apply, mul_comm]

/-- **The sign of the orientation of two velocities read in a chart.** -/
theorem b3Rest2_sign_orient (hE : Module.finrank ℂ E = 1) {γ₁ γ₂ : ℝ → C}
    (h₁ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ₁) (h₂ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ₂) {x : C}
    {t s : ℝ} (heq : γ₁ t = γ₂ s) (hsrc : γ₁ t ∈ (chartAt E x).source) :
    SignType.sign ((conj ((b3Rest_L hE).symm (deriv (chartAt E x ∘ γ₁) t)) *
        (b3Rest_L hE).symm (deriv (chartAt E x ∘ γ₂) s)).im) =
      SignType.sign (b3_orient E (b3_velocity E C γ₁ t) (b3_velocity E C γ₂ s)) := by
  set p := γ₁ t
  have hu : chartAt E p p ∈ b3Forms_trDom p x :=
    ⟨(chartAt E p).map_source (mem_chart_source E p), by
      rw [mem_preimage, (chartAt E p).left_inv (mem_chart_source E p)]; exact hsrc⟩
  have hd1 := b3Forms_deriv_chart_comp h₁ hsrc
  have hd2 := b3Forms_deriv_chart_comp h₂ (heq ▸ hsrc)
  rw [← heq] at hd2
  rw [b3Forms_fderiv_tr_real hu] at hd1 hd2
  obtain ⟨μ, hμ⟩ := b3Rest2_line_mul hE (fderiv ℂ (b3Forms_tr (E := E) p x) (chartAt E p p))
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hdet := b3Forms_det_fderiv_tr_complex_ne_zero hu
    have hinj : Function.Injective
        (fderiv ℂ (b3Forms_tr (E := E) p x) (chartAt E p p) : E →ₗ[ℂ] E) :=
      ((Module.End.isUnit_iff _).1
        ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))).1
    have h1 := hμ 1
    rw [h0, zero_mul, b3Rest_L_apply, one_smul] at h1
    apply b3Rest_e_ne_zero hE
    apply hinj
    have : (fderiv ℂ (b3Forms_tr (E := E) p x) (chartAt E p p)) (b3Rest_e hE) = 0 := by
      have := congrArg (b3Rest_L hE) h1
      rwa [ContinuousLinearEquiv.apply_symm_apply, _root_.map_zero] at this
    simpa using this
  set v₁ := b3_velocity E C γ₁ t
  set v₂ := b3_velocity E C γ₂ s
  have e1 : (b3Rest_L hE).symm (deriv (chartAt E x ∘ γ₁) t) = μ * (b3Rest_L hE).symm v₁ := by
    rw [hd1, ContinuousLinearMap.coe_restrictScalars']
    conv_lhs => rw [← (b3Rest_L hE).apply_symm_apply (b3Forms_velocity γ₁ t)]
    exact hμ _
  have e2 : (b3Rest_L hE).symm (deriv (chartAt E x ∘ γ₂) s) = μ * (b3Rest_L hE).symm v₂ := by
    rw [hd2, ContinuousLinearMap.coe_restrictScalars']
    conv_lhs => rw [← (b3Rest_L hE).apply_symm_apply (b3Forms_velocity γ₂ s)]
    exact hμ _
  obtain ⟨κ, hκ, hor⟩ := b3Rest2_orient_L hE
  rw [e1, e2, b3Rest2_sign_normSq_mul hμ0]
  conv_rhs => rw [← (b3Rest_L hE).apply_symm_apply v₁, ← (b3Rest_L hE).apply_symm_apply v₂, hor]
  rw [b3Rest2_sign_pos_mul hκ]

end HodgeLean.Foundations.Program
