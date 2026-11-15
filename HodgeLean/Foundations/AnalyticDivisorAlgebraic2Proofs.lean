import HodgeLean.Foundations.AnalyticDivisorAlgebraic

/-! # Proof obligations for the analytic divisor spec, second stage

One obligation per statement of `HodgeLean.Foundations.AnalyticDivisorAlgebraic2`. All eight are proved, by three parallel provers.
-/

noncomputable section

open Set Filter Topology Metric Complex

open scoped Real

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic2

open AppellHumbert

/-- The multi-index geometric series over any complete normed field, together with the absolute
summability that the induction needs. -/
theorem hasSum_prod_geometric_and_summable_norm {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (n : ℕ) :
    ∀ (u : Fin n → 𝕜), (∀ i, ‖u i‖ < 1) →
    HasSum (fun α : Fin n → ℕ => ∏ i, u i ^ α i) (∏ i, (1 - u i)⁻¹) ∧
      Summable (fun α : Fin n → ℕ => ‖∏ i, u i ^ α i‖) := by
  induction n with
  | zero =>
    intro u _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
    exact ⟨by simp, (hasSum_fintype _).summable⟩
  | succ n ihn =>
    intro u hu
    obtain ⟨ih, ihn⟩ := ihn (fun i => u (Fin.succ i)) fun i => hu _
    have h0 := hasSum_geometric_of_norm_lt_one (hu 0)
    have h0n : Summable fun k : ℕ => ‖u 0 ^ k‖ := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hu 0)
    have hmn : Summable fun x : ℕ × (Fin n → ℕ) =>
        ‖u 0 ^ x.1‖ * ‖∏ i : Fin n, u (Fin.succ i) ^ x.2 i‖ :=
      h0n.mul_of_nonneg ihn (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hs : Summable fun x : ℕ × (Fin n → ℕ) =>
        u 0 ^ x.1 * ∏ i : Fin n, u (Fin.succ i) ^ x.2 i :=
      summable_mul_of_summable_norm (f := fun k : ℕ => u 0 ^ k)
        (g := fun α : Fin n → ℕ => ∏ i : Fin n, u (Fin.succ i) ^ α i) h0n ihn
    have hm := HasSum.mul (f := fun k : ℕ => u 0 ^ k)
        (g := fun α : Fin n → ℕ => ∏ i : Fin n, u (Fin.succ i) ^ α i) h0 ih hs
    rw [← Fin.prod_univ_succ (f := fun i => (1 - u i)⁻¹)] at hm
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    refine ⟨(e.hasSum_iff).mp ?_, (e.summable_iff).mp ?_⟩
    · refine hm.congr_fun fun x => ?_
      simp [e, Fin.consEquiv, Fin.prod_univ_succ]
    · refine hmn.congr fun x => ?_
      simp [e, Fin.consEquiv, Fin.prod_univ_succ, norm_mul]

theorem spec_hasSum_prod_geometric_aux {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ < 1) :
    HasSum (fun α : Fin n → ℕ => ∏ i, u i ^ α i) (∏ i, (1 - u i)⁻¹) := 
  (hasSum_prod_geometric_and_summable_norm n u hu).1

section Polydisc

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem mem_closedBall_fin_iff {c w : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    w ∈ closedBall c r ↔ ∀ i, ‖w i - c i‖ ≤ r := by
  simp only [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hr, Pi.sub_apply]

theorem mem_ball_fin_iff {c w : Fin n → ℂ} {r : ℝ} (hr : 0 < r) :
    w ∈ ball c r ↔ ∀ i, ‖w i - c i‖ < r := by
  simp only [mem_ball, dist_eq_norm, pi_norm_lt_iff hr, Pi.sub_apply]

omit [CompleteSpace E] in
/-- The Cauchy kernel times a function continuous on the closed polydisc is integrable over the
distinguished boundary. -/
theorem torusIntegrable_cauchyKernel {f : (Fin n → ℂ) → E} {c z : Fin n → ℂ} {r : ℝ}
    (hf : ContinuousOn f (closedBall c r)) (hz : z ∈ ball c r) :
    TorusIntegrable (fun w => (∏ i, (w i - z i))⁻¹ • f w) c (fun _ => r) := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hzi := (mem_ball_fin_iff hr).1 hz
  have hmem : ∀ θ : Fin n → ℝ, ∀ i, ‖torusMap c (fun _ => r) θ i - c i‖ = r := by
    intro θ i
    simp [torusMap, norm_exp_ofReal_mul_I, abs_of_pos hr]
  have hne : ∀ θ : Fin n → ℝ, ∀ i, torusMap c (fun _ => r) θ i - z i ≠ 0 := by
    intro θ i h
    have h1 := hmem θ i
    have : torusMap c (fun _ => r) θ i - c i = z i - c i := by
      rw [← sub_add_sub_cancel _ (z i), h, zero_add]
    rw [this] at h1
    exact (hzi i).ne h1
  have hcont : Continuous fun θ : Fin n → ℝ => torusMap c (fun _ => r) θ := by
    unfold torusMap; fun_prop
  have hfc : Continuous fun θ : Fin n → ℝ => f (torusMap c (fun _ => r) θ) :=
    hf.comp_continuous hcont fun θ => (mem_closedBall_fin_iff hr.le).2 fun i => (hmem θ i).le
  have hk : Continuous fun θ : Fin n → ℝ => (∏ i, (torusMap c (fun _ => r) θ i - z i))⁻¹ := by
    refine Continuous.inv₀ ?_ fun θ => Finset.prod_ne_zero_iff.2 fun i _ => hne θ i
    refine continuous_finsetProd _ fun i _ => ?_
    exact ((continuous_apply i).comp hcont).sub continuous_const
  exact (hk.smul hfc).integrableOn_Icc

theorem differentiable_fin_cons_right (x : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; fun_prop
  · simp only [Fin.cons_succ]; fun_prop

theorem differentiable_fin_cons_left (y : Fin n → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; fun_prop
  · simp only [Fin.cons_succ]; fun_prop

theorem torusIntegral_cauchy : ∀ {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (_hU : IsOpen U) (_hf : DifferentiableOn ℂ f U) {c : Fin n → ℂ} {r : ℝ}
    (_hcU : closedBall c r ⊆ U) {z : Fin n → ℂ} (_hz : z ∈ ball c r),
    (∯ w in T(c, fun _ => r), (∏ i, (w i - z i))⁻¹ • f w) = (2 * π * I) ^ n • f z := by
  induction n with
  | zero =>
    intro f U _ _ c r _ z _
    simp [Subsingleton.elim c z]
  | succ n ih =>
    intro f U hU hf c r hcU z hz
    have hr : 0 < r := pos_of_mem_ball hz
    have hzi := (mem_ball_fin_iff hr).1 hz
    have hint := torusIntegrable_cauchyKernel (hf.continuousOn.mono hcU) hz
    rw [torusIntegral_succ hint]
    -- the inner integral, for `x` on the circle
    have hinner : ∀ x ∈ sphere (c 0) r,
        (∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i))⁻¹ • f (Fin.cons x y)) =
        (2 * π * I) ^ n • ((x - z 0)⁻¹ • f (Fin.cons x (Fin.tail z))) := by
      intro x hx
      have hx' : ‖x - c 0‖ = r := by simpa [dist_eq_norm] using hx
      have hsplit : ∀ y : Fin n → ℂ,
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i))⁻¹ • f (Fin.cons x y) =
          (x - z 0)⁻¹ • ((∏ i, (y i - Fin.tail z i))⁻¹ • f (Fin.cons x y)) := by
        intro y
        rw [Fin.prod_univ_succ, mul_inv, mul_smul]
        simp [Fin.tail]
      simp_rw [hsplit]
      rw [torusIntegral_smul]
      have hball : Fin.tail z ∈ ball (c ∘ Fin.succ) r :=
        (mem_ball_fin_iff hr).2 fun i => hzi (Fin.succ i)
      have hcons := differentiable_fin_cons_right (n := n) x
      have hU' : IsOpen ((fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) ⁻¹' U) :=
        hU.preimage hcons.continuous
      have hf' : DifferentiableOn ℂ (fun y => f (Fin.cons x y))
          ((fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) ⁻¹' U) := fun y hy =>
        ((hf _ hy).differentiableAt (hU.mem_nhds hy)).comp y (hcons y) |>.differentiableWithinAt
      have hcU' : closedBall (c ∘ Fin.succ) r ⊆
          (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) ⁻¹' U := by
        intro y hy
        apply hcU
        rw [mem_closedBall_fin_iff hr.le] at hy ⊢
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx'.le
        · simpa using hy j
      have := ih hU' hf' hcU' hball
      simp only [Function.comp_def] at this ⊢
      rw [this, smul_comm]
    rw [circleIntegral.integral_congr hr.le hinner, circleIntegral.integral_smul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) := by
      intro x hx
      have hx' : ‖x - c 0‖ ≤ r := by simpa [dist_eq_norm] using hx
      have hmem : (Fin.cons x (Fin.tail z) : Fin (n + 1) → ℂ) ∈ U := by
        apply hcU
        rw [mem_closedBall_fin_iff hr.le]
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx'
        · simpa [Fin.tail] using (hzi j.succ).le
      exact (((hf _ hmem).differentiableAt (hU.mem_nhds hmem)).comp x
        (differentiable_fin_cons_left _ x)).differentiableWithinAt
    have hz0 : z 0 ∈ ball (c 0) r := by simpa [dist_eq_norm] using hzi 0
    rw [hd.circleIntegral_sub_inv_smul hz0, Fin.cons_self_tail, smul_smul, ← pow_succ]

theorem spec_torusIntegral_cauchy_aux {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {c : Fin n → ℂ} {r : ℝ}
    (hcU : closedBall c r ⊆ U) {z : Fin n → ℂ} (hz : z ∈ ball c r) :
    (∯ w in T(c, fun _ => r), (∏ i, (w i - z i))⁻¹ • f w) = (2 * π * I) ^ n • f z := 
  torusIntegral_cauchy hU hf hcU hz

open MeasureTheory in
theorem spec_analyticAt_torusCauchyIntegral_aux {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (closedBall c r)) :
    AnalyticAt ℂ (fun z => ∯ w in T(c, fun _ => r), (∏ i, (w i - z i))⁻¹ • f w) c := by
  set R : Fin n → ℝ := fun _ => r with hR
  have hGa : AnalyticAt ℂ (fun u : Fin n → ℂ => ∏ i, (1 - u i)⁻¹) 0 := by
    refine Finset.analyticAt_fun_prod _ fun i _ => ?_
    refine (analyticAt_const.sub ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt 0)).inv ?_
    simp
  obtain ⟨q, ρ, hq⟩ := hGa
  obtain ⟨ρ0, hρ0, hρ0ρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq.r_pos
  have hρ0' : (0 : ℝ) < ρ0 := by exact_mod_cast hρ0
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hf
  -- the torus lies in the closed polydisc
  have hsub : ∀ θ : Fin n → ℝ, ∀ i, torusMap c R θ i - c i = r * exp (θ i * I) := by
    intro θ i; simp [torusMap, hR]
  have hne : ∀ θ : Fin n → ℝ, ∀ i, torusMap c R θ i - c i ≠ 0 := by
    intro θ i; rw [hsub]; exact mul_ne_zero (by exact_mod_cast hr.ne') (exp_ne_zero _)
  have hnorm : ∀ θ : Fin n → ℝ, ∀ i, ‖torusMap c R θ i - c i‖ = r := by
    intro θ i; rw [hsub, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  have hmem : ∀ θ, torusMap c R θ ∈ closedBall c r := by
    intro θ
    rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hr.le]
    intro i; exact (hnorm θ i).le
  have hfw : ∀ θ, ‖f (torusMap c R θ)‖ ≤ M := fun θ => hM _ (hmem θ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfw 0)
  have htc : Continuous (torusMap c R) := by
    unfold torusMap; fun_prop
  have hfc : Continuous fun θ => f (torusMap c R θ) := hf.comp_continuous htc hmem
  -- the coefficient integrand
  let b : (Fin n → ℂ) → (Fin n → ℂ) := fun w i => (w i - c i)⁻¹
  have hb : ∀ θ, ‖b (torusMap c R θ)‖ ≤ r⁻¹ := by
    intro θ
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [b, norm_inv, hnorm]; rfl
  have hbc : Continuous fun θ => b (torusMap c R θ) := by
    refine continuous_pi fun i => ?_
    exact ((continuous_apply i).comp htc |>.sub continuous_const).inv₀ (hne · i)
  have hkc : Continuous fun θ => (∏ i, (torusMap c R θ i - c i))⁻¹ := by
    refine Continuous.inv₀ ?_ ?_
    · exact continuous_finsetProd _ fun i _ => (continuous_apply i).comp htc |>.sub continuous_const
    · intro θ; exact Finset.prod_ne_zero_iff.2 fun i _ => hne θ i
  have hkn : ∀ θ, ‖(∏ i, (torusMap c R θ i - c i))⁻¹‖ = (r ^ n)⁻¹ := by
    intro θ; rw [norm_inv, norm_prod]; simp [hnorm]
  let T : (m : ℕ) → (Fin n → ℂ) → ContinuousMultilinearMap ℂ (fun _ : Fin m => Fin n → ℂ) E :=
    fun m w => (∏ i, (w i - c i))⁻¹ •
      ((q m).compContinuousLinearMap (fun _ => ContinuousLinearMap.mul ℂ (Fin n → ℂ) (b w))).smulRight
        (f w)
  let P : FormalMultilinearSeries ℂ (Fin n → ℂ) E := fun m => ∯ w in T(c, R), T m w
  have hTn : ∀ m θ, ‖T m (torusMap c R θ)‖ ≤ (r ^ n)⁻¹ * (‖q m‖ * (r⁻¹) ^ m * M) := by
    intro m θ
    simp only [T, norm_smul, ContinuousMultilinearMap.norm_smulRight, hkn]
    gcongr
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact (ContinuousLinearMap.opNorm_mul_apply_le _ _ (b _)).trans (hb θ)
    exact hfw θ
  have hTc : ∀ m, Continuous fun θ => T m (torusMap c R θ) := by
    intro m
    refine hkc.smul ?_
    have h1 : Continuous fun θ => (q m).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.mul ℂ (Fin n → ℂ) (b (torusMap c R θ))) := by
      have := (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin m => Fin n → ℂ) (fun _ : Fin m => Fin n → ℂ) ℂ).cont.comp
        (continuous_pi fun _ => (ContinuousLinearMap.mul ℂ (Fin n → ℂ)).continuous.comp hbc)
      exact this.clm_apply continuous_const
    have := (ContinuousMultilinearMap.smulRightL ℂ (fun _ : Fin m => Fin n → ℂ) E).continuous₂.comp
      (h1.prodMk hfc)
    simp only [Function.comp_def, Function.uncurry_apply_pair] at this
    exact this

  have hPn : ∀ m, ‖P m‖ ≤ (2 * π) ^ n * (‖q m‖ * (r⁻¹) ^ m * M) := by
    intro m
    refine (norm_torusIntegral_le_of_norm_le_const (hTn m)).trans (le_of_eq ?_)
    rw [show ∏ i, |R i| = r ^ n by simp [hR, abs_of_pos hr], mul_assoc, ← mul_assoc (r ^ n),
      mul_inv_cancel₀ (by positivity), one_mul]
  have hρq : (ρ0 : ENNReal) < q.radius := hρ0ρ.trans_le hq.r_le
  obtain ⟨C, hC, hqC⟩ := q.norm_mul_pow_le_of_lt_radius hρq
  have hρ' : ((r.toNNReal * ρ0 : NNReal) : ℝ) = r * ρ0 := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hr.le]
  have hPr : ((r.toNNReal * ρ0 : NNReal) : ENNReal) ≤ P.radius := by
    refine P.le_radius_of_bound ((2 * π) ^ n * M * C) fun m => ?_
    rw [hρ']
    calc ‖P m‖ * (r * ρ0) ^ m ≤ (2 * π) ^ n * (‖q m‖ * (r⁻¹) ^ m * M) * (r * ρ0) ^ m := by
          gcongr; exact hPn m
      _ = (2 * π) ^ n * M * (‖q m‖ * (ρ0 : ℝ) ^ m) := by
          rw [mul_pow, inv_pow]; field_simp; ring
      _ ≤ (2 * π) ^ n * M * C := by gcongr; exact hqC m
  refine ⟨P, (r.toNNReal * ρ0 : NNReal), hPr, ?_, ?_⟩
  · exact ENNReal.coe_pos.2 (mul_pos (Real.toNNReal_pos.2 hr) (ENNReal.coe_pos.1 hρ0))
  intro y hy
  have hy' : ‖y‖ < r * ρ0 := by
    have : ‖y‖ₑ < (r.toNNReal : ENNReal) * ρ0 := by
      simpa [Metric.mem_eball, edist_eq_enorm_sub] using hy
    rw [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_lt_coe] at this
    rw [← hρ']; exact_mod_cast this
  set s : ℝ := ‖y‖ / r with hs
  have hs0 : 0 ≤ s := by positivity
  have hsρ : s < ρ0 := by rw [hs, div_lt_iff₀ hr]; linarith
  let s' : NNReal := ⟨s, hs0⟩
  have hsq : (s' : ENNReal) < q.radius :=
    (ENNReal.coe_lt_coe.2 (show s' < ρ0 from hsρ)).trans hρq
  let J : (Fin n → ℝ) → ℂ := fun θ => ∏ i, (R i : ℂ) * exp (θ i * I) * I
  have hJc : Continuous J := by fun_prop
  have hJn : ∀ θ, ‖J θ‖ = r ^ n := by
    intro θ; simp [J, norm_prod, hR, abs_of_pos hr, norm_exp_ofReal_mul_I]
  have hby : ∀ θ, ‖b (torusMap c R θ) * y‖ ≤ s := by
    intro θ
    refine (norm_mul_le _ _).trans ?_
    rw [hs, div_eq_inv_mul]; gcongr; exact hb θ
  have hPy : ∀ m, P m (fun _ => y) =
      ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π), (J θ • T m (torusMap c R θ)) (fun _ => y) := by
    intro m
    exact ContinuousMultilinearMap.integral_apply
      ((hJc.smul (hTc m)).continuousOn.integrableOn_compact isCompact_Icc) _
  simp_rw [hPy]
  refine hasSum_integral_of_dominated_convergence (fun m _ => M * (‖q m‖ * s ^ m)) ?_ ?_ ?_ ?_ ?_
  · intro m
    exact ((ContinuousMultilinearMap.apply ℂ _ E (fun _ => y)).continuous.comp
      (hJc.smul (hTc m))).aestronglyMeasurable
  · intro m
    refine Filter.Eventually.of_forall fun θ => ?_
    simp only [T, smul_apply, ContinuousMultilinearMap.smulRight_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.mul_apply',
      norm_smul, hJn, hkn]
    have hq1 : ‖q m (fun _ => b (torusMap c R θ) * y)‖ ≤ ‖q m‖ * s ^ m := by
      refine ((q m).le_opNorm _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      gcongr; exact hby θ
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, mul_comm M]
    gcongr
    exact hfw θ
  · exact Filter.Eventually.of_forall fun θ => (q.summable_norm_mul_pow hsq).mul_left M
  · exact integrableOn_const measure_Icc_lt_top.ne
  · refine Filter.Eventually.of_forall fun θ => ?_
    have hmemb : b (torusMap c R θ) * y ∈ Metric.eball (0 : Fin n → ℂ) ρ := by
      rw [Metric.mem_eball, edist_zero_right]
      refine lt_of_le_of_lt ?_ (hρ0ρ)
      have : ‖b (torusMap c R θ) * y‖₊ ≤ ρ0 := by
        rw [← NNReal.coe_le_coe, coe_nnnorm]; exact (hby θ).trans hsρ.le
      exact_mod_cast this
    have h2 := (((hq.hasSum hmemb).smul_const (f (torusMap c R θ))).const_smul
      (∏ i, (torusMap c R θ i - c i))⁻¹).const_smul (J θ)
    convert h2 using 1
    · funext m
      simp only [T, smul_apply, ContinuousMultilinearMap.smulRight_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.mul_apply']
    · simp only [J, smul_smul, zero_add]
      congr 2
      rw [← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_inv, Pi.mul_apply, mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ (hne θ i),
        one_mul, Pi.add_apply, sub_sub]

theorem spec_analyticOnNhd_of_differentiableOn_fin_aux {f : (Fin n → ℂ) → E}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U := by
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  have hr : 0 < ε / 2 := half_pos hε
  have hcU : closedBall x (ε / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hF := spec_analyticAt_torusCauchyIntegral_aux (f := f) (c := x) hr
    ((hf.mono hcU).continuousOn)
  have hne : ((2 * π * I) ^ n : ℂ) ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  refine (hF.const_smul (c := ((2 * π * I) ^ n)⁻¹)).congr ?_
  filter_upwards [ball_mem_nhds x hr] with z hz
  rw [Pi.smul_apply, spec_torusIntegral_cauchy_aux hU hf hcU hz, smul_smul, inv_mul_cancel₀ hne,
    one_smul]

end Polydisc

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem spec_analyticOnNhd_of_differentiableOn_aux {f : V → E} {U : Set V} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  let e : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  have hg : AnalyticOnNhd ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    spec_analyticOnNhd_of_differentiableOn_fin_aux (hU.preimage e.symm.continuous)
      (hf.comp e.symm.differentiableOn (fun _ h => h))
  intro x hx
  have := (hg (e x) (by simpa using hx)).comp
    ((e : V →L[ℂ] (Fin (Module.finrank ℂ V) → ℂ)).analyticAt x)
  simpa [Function.comp_def] using this

theorem spec_isClosedAnalytic_zeroSet_of_differentiable_aux {f : V → ℂ}
    (hf : Differentiable ℂ f) : IsClosedAnalytic V {v | f v = 0} :=
  AnalyticDivisorAlgebraic.spec_isClosedAnalytic_zeroSet f
    (spec_analyticOnNhd_of_differentiableOn_aux isOpen_univ hf.differentiableOn)

theorem spec_isClosedAnalytic_theta_aux (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) : IsClosedAnalytic V {v | θ v = 0} :=
  spec_isClosedAnalytic_zeroSet_of_differentiable_aux hθ.1

end FiniteDimensional

theorem spec_separately_analytic_not_continuousAt_aux :
    (∀ y : ℝ, AnalyticOnNhd ℝ (fun x : ℝ => x * y / (x ^ 2 + y ^ 2)) univ) ∧
    (∀ x : ℝ, AnalyticOnNhd ℝ (fun y : ℝ => x * y / (x ^ 2 + y ^ 2)) univ) ∧
    ¬ ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) (0, 0) := by
  refine ⟨fun y => ?_, fun x => ?_, ?_⟩
  · rcases eq_or_ne y 0 with rfl | hy
    · simp only [mul_zero, zero_div]; exact fun _ _ => analyticAt_const
    · intro x _
      exact ((analyticAt_id.mul analyticAt_const).div (by fun_prop) (by positivity))
  · rcases eq_or_ne x 0 with rfl | hx
    · simp only [zero_mul, zero_div]; exact fun _ _ => analyticAt_const
    · intro y _
      exact ((analyticAt_const.mul analyticAt_id).div (by fun_prop) (by positivity))
  · intro h
    have hd : Tendsto (fun t : ℝ => ((t, t) : ℝ × ℝ)) (𝓝[≠] 0) (𝓝 (0, 0)) :=
      ((continuous_id.prodMk continuous_id).tendsto' 0 (0, 0) rfl).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun p : ℝ × ℝ => p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) (𝓝 (0, 0))
        (𝓝 0) := by simpa using h.tendsto
    have h3 : (fun t : ℝ => (fun p : ℝ × ℝ => p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) (t, t))
        =ᶠ[𝓝[≠] 0] fun _ => (1 / 2 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have : t ≠ 0 := ht
      field_simp; ring
    have h4 := tendsto_nhds_unique (h2.comp hd) (tendsto_const_nhds.congr' h3.symm)
    norm_num at h4

end HodgeLean.Foundations.AnalyticDivisorAlgebraic2
