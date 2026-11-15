import HodgeLean.Foundations.Program.CurveJacobianRestArc
import HodgeLean.Foundations.Program.CurveJacobianRestPD

/-! # Track B3, lane Rest2: the local degree of a smeared arc along a transverse path

In the complex plane, let `c` be a `C¹` arc on `[a, b]` and `d` a `C¹` path on `[s₀, s₁]`, crossing
`c` transversally at finitely many interior points. The smeared arc `K(z) = ∫ ρ_ε(z - c t) c'(t) dt`
satisfies, for small `ε`,
`∫_{s₀}^{s₁} Im (conj K(d s) · d'(s)) ds = (∫ ρ_ε) · Σ_{crossings} sign Im (conj c'(t) · d'(s))`
(`b3Rest2_degree`). The integrand is `ρ_ε(Φ(s, t)) J(s, t)` with `Φ(s, t) = d s - c t` and
`J = Im (conj c' · d')`, the Jacobian determinant of `Φ`. Near each crossing `Φ` is a local
diffeomorphism (inverse function theorem) onto a neighbourhood of `0`, so its contribution is
`sign J · ∫ ρ_ε` by the change of variables formula; away from the crossings `|Φ|` is bounded
below, and the integrand vanishes once `ε` is smaller.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ComplexConjugate

namespace HodgeLean.Foundations.Program

/-- The real-linear map `u ↦ Re u · d' - Im u · c'` of `ℂ`, the derivative of
`s + i t ↦ d s - c t`. -/
def b3Rest2_D (d' c' : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight d' - Complex.imCLM.smulRight c'

theorem b3Rest2_D_apply (d' c' u : ℂ) :
    b3Rest2_D d' c' u = (u.re : ℂ) * d' - (u.im : ℂ) * c' := by
  simp [b3Rest2_D, Complex.real_smul]

theorem b3Rest2_det_D (d' c' : ℂ) :
    LinearMap.det (b3Rest2_D d' c' : ℂ →ₗ[ℝ] ℂ) = (conj c' * d').im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, b3Rest2_D_apply]
  ring

theorem b3Rest2_hasFDerivAt_Φ {d d' c c' : ℝ → ℂ} {q : ℂ} (hd : HasDerivAt d (d' q.re) q.re)
    (hc : HasDerivAt c (c' q.im) q.im) :
    HasFDerivAt (fun z : ℂ ↦ d z.re - c z.im) (b3Rest2_D (d' q.re) (c' q.im)) q := by
  have h1 := (show HasFDerivAt d _ (Complex.reCLM q) from hd.hasFDerivAt).comp q
    Complex.reCLM.hasFDerivAt
  have h2 := (show HasFDerivAt c _ (Complex.imCLM q) from hc.hasFDerivAt).comp q
    Complex.imCLM.hasFDerivAt
  refine (h1.sub h2).congr_fderiv ?_
  ext u
  apply Complex.ext <;> simp [b3Rest2_D_apply, Complex.real_smul]

theorem b3Rest2_hasStrictFDerivAt_Φ {d d' c c' : ℝ → ℂ} {q : ℂ}
    (hd : ∀ᶠ s in 𝓝 q.re, HasDerivAt d (d' s) s) (hd' : ContinuousAt d' q.re)
    (hc : ∀ᶠ t in 𝓝 q.im, HasDerivAt c (c' t) t) (hc' : ContinuousAt c' q.im) :
    HasStrictFDerivAt (fun z : ℂ ↦ d z.re - c z.im) (b3Rest2_D (d' q.re) (c' q.im)) q := by
  have h1 := (show HasStrictFDerivAt d _ (Complex.reCLM q) from
    (hasStrictDerivAt_of_hasDerivAt_of_continuousAt hd hd').hasStrictFDerivAt).comp q
    Complex.reCLM.hasStrictFDerivAt
  have h2 := (show HasStrictFDerivAt c _ (Complex.imCLM q) from
    (hasStrictDerivAt_of_hasDerivAt_of_continuousAt hc hc').hasStrictFDerivAt).comp q
    Complex.imCLM.hasStrictFDerivAt
  refine (h1.sub h2).congr_fderiv ?_
  ext u
  apply Complex.ext <;> simp [b3Rest2_D_apply, Complex.real_smul]

theorem b3Rest2_sign_eq_of_mul_pos {x y : ℝ} (h : 0 < x * y) :
    SignType.sign y = SignType.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : y < 0 := by nlinarith
    rw [sign_neg hx, sign_neg this]
  · rw [hx, zero_mul] at h; exact absurd h (lt_irrefl _)
  · have : 0 < y := by nlinarith
    rw [sign_pos hx, sign_pos this]

/-- **Local inversion at a transverse crossing.** -/
theorem b3Rest2_local_inv {O : Set ℝ} (hO : IsOpen O) {a b : ℝ} {d d' c c' : ℝ → ℂ}
    (hd : ∀ s ∈ O, HasDerivAt d (d' s) s) (hd' : ContinuousOn d' O) (hc' : Continuous c')
    (hcd : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t) {p : ℂ} (hpO : p.re ∈ O)
    (hpab : p.im ∈ Ioo a b) (hp0 : d p.re = c p.im)
    (htr : (conj (c' p.im) * d' p.re).im ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧ W ⊆ ball p r ∧ (∀ q ∈ W, q.re ∈ O ∧ q.im ∈ Ioo a b) ∧
      InjOn (fun z : ℂ ↦ d z.re - c z.im) W ∧
      (∀ q ∈ W, SignType.sign (conj (c' q.im) * d' q.re).im =
        SignType.sign (conj (c' p.im) * d' p.re).im) ∧
      ∃ ε > 0, ball 0 ε ⊆ (fun z : ℂ ↦ d z.re - c z.im) '' W := by
  set Φ : ℂ → ℂ := fun z ↦ d z.re - c z.im
  set J : ℂ → ℝ := fun q ↦ (conj (c' q.im) * d' q.re).im
  set Dp := b3Rest2_D (d' p.re) (c' p.im)
  have hdet : LinearMap.det (Dp : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by rw [b3Rest2_det_D]; exact htr
  have hbij : Function.Bijective (Dp : ℂ →ₗ[ℝ] ℂ) := (Module.End.isUnit_iff _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  let eqv : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (Dp : ℂ →ₗ[ℝ] ℂ) hbij).toContinuousLinearEquiv
  have heqv : (eqv : ℂ →L[ℝ] ℂ) = Dp := by
    ext u <;> rfl
  have hU1o : IsOpen {q : ℂ | q.re ∈ O ∧ q.im ∈ Ioo a b} :=
    (hO.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  have hstrict : HasStrictFDerivAt Φ (eqv : ℂ →L[ℝ] ℂ) p := by
    rw [heqv]
    refine b3Rest2_hasStrictFDerivAt_Φ ?_ (hd'.continuousAt (hO.mem_nhds hpO)) ?_
      hc'.continuousAt
    · filter_upwards [hO.mem_nhds hpO] with s hs using hd s hs
    · filter_upwards [isOpen_Ioo.mem_nhds hpab] with t ht using hcd t ht
  set PH := hstrict.toOpenPartialHomeomorph Φ
  have hPH : (PH : ℂ → ℂ) = Φ := hstrict.toOpenPartialHomeomorph_coe
  have hJc : ContinuousOn (fun q ↦ J p * J q) {q : ℂ | q.re ∈ O ∧ q.im ∈ Ioo a b} := by
    refine continuousOn_const.mul ?_
    refine Complex.continuous_im.comp_continuousOn ?_
    refine ((Complex.continuous_conj.comp (hc'.comp Complex.continuous_im)).continuousOn).mul ?_
    exact hd'.comp Complex.continuous_re.continuousOn fun q hq ↦ hq.1
  set S := {q : ℂ | q.re ∈ O ∧ q.im ∈ Ioo a b} ∩ (fun q ↦ J p * J q) ⁻¹' Ioi 0
  have hSo : IsOpen S := hJc.isOpen_inter_preimage hU1o isOpen_Ioi
  set W := PH.source ∩ S ∩ ball p r
  have hWo : IsOpen W := (PH.open_source.inter hSo).inter isOpen_ball
  have hpW : p ∈ W := by
    refine ⟨⟨hstrict.mem_toOpenPartialHomeomorph_source, ⟨hpO, hpab⟩, ?_⟩, mem_ball_self hr⟩
    show 0 < J p * J p
    exact mul_self_pos.2 htr
  have hWs : W ⊆ PH.source := fun q hq ↦ hq.1.1
  refine ⟨W, hWo, hpW, fun q hq ↦ hq.2, fun q hq ↦ hq.1.2.1, ?_, fun q hq ↦
    b3Rest2_sign_eq_of_mul_pos hq.1.2.2, ?_⟩
  · rw [← hPH]; exact PH.injOn.mono hWs
  · have himo : IsOpen (Φ '' W) := by rw [← hPH]; exact PH.isOpen_image_of_subset_source hWo hWs
    have h0 : (0 : ℂ) ∈ Φ '' W := ⟨p, hpW, by simp [Φ, hp0]⟩
    exact Metric.isOpen_iff.1 himo 0 h0

/-- **Iterated integrals over a rectangle of `ℂ = ℝ²`.** -/
theorem b3Rest2_iterated_eq {g : ℂ → ℝ} {s0 s1 a b : ℝ} (hs : s0 ≤ s1) (hab : a ≤ b)
    (hg : IntegrableOn g {q : ℂ | q.re ∈ Icc s0 s1 ∧ q.im ∈ Icc a b}) :
    ∫ s in s0..s1, ∫ t in a..b, g ⟨s, t⟩ =
      ∫ q in {q : ℂ | q.re ∈ Icc s0 s1 ∧ q.im ∈ Icc a b}, g q := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hme := Complex.measurableEquivRealProd.measurableEmbedding
  have hpre : (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ) ⁻¹' (Icc s0 s1 ×ˢ Icc a b) =
      {q : ℂ | q.re ∈ Icc s0 s1 ∧ q.im ∈ Icc a b} := rfl
  set G : ℝ × ℝ → ℝ := fun p ↦ g ⟨p.1, p.2⟩
  have hGg : ∀ q : ℂ, G (Complex.measurableEquivRealProd q) = g q := fun q ↦ rfl
  have hGi : IntegrableOn G (Icc s0 s1 ×ˢ Icc a b) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, ← hmp.integrableOn_comp_preimage hme, hpre]
    exact hg
  have h1 := hmp.setIntegral_preimage_emb hme G (Icc s0 s1 ×ˢ Icc a b)
  rw [hpre] at h1
  simp only [hGg] at h1
  rw [h1, Measure.volume_eq_prod, setIntegral_prod G hGi, intervalIntegral.integral_of_le hs,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ ↦ ?_
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

open scoped Classical in
/-- The integrand `ρ_ε(d s - c t) Im (conj c'(t) d'(s))` at `q = s + i t`, for `s ∈ O`. -/
def b3Rest2_F (O : Set ℝ) (d d' c c' : ℝ → ℂ) (ε : ℝ) (q : ℂ) : ℝ :=
  if q.re ∈ O then b3Rest_rho ε (d q.re - c q.im) * (conj (c' q.im) * d' q.re).im else 0

/-- The integrand of the smeared arc along `d` is the inner integral of `b3Rest2_F`. -/
theorem b3Rest2_inner_eq (O : Set ℝ) {d d' c c' : ℝ → ℂ} (hc : Continuous c)
    (hc' : Continuous c') (ε a b s : ℝ) :
    O.indicator (fun s ↦ (conj (b3Rest_arcK ε c c' a b (d s)) * d' s).im) s =
      ∫ t in a..b, b3Rest2_F O d d' c c' ε ⟨s, t⟩ := by
  by_cases hs : s ∈ O
  · rw [indicator_of_mem hs]
    simp only [b3Rest2_F, hs, ite_true]
    set w := d' s
    let L : ℂ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun z ↦ (conj z * w).im
        map_add' := fun z z' ↦ by simp [add_mul]
        map_smul' := fun r z ↦ by simp [Complex.real_smul, mul_assoc] }
    have hL : ∀ z, L z = (conj z * w).im := fun z ↦ rfl
    have hint : IntervalIntegrable (fun t ↦ (b3Rest_rho ε (d s - c t) : ℂ) * c' t) volume a b :=
      ((Complex.continuous_ofReal.comp ((b3Rest_rho_contDiff ε).continuous.comp
        (continuous_const.sub hc))).mul hc').intervalIntegrable a b
    rw [b3Rest_arcK, ← hL, ← L.intervalIntegral_comp_comm hint]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [hL, map_mul, Complex.conj_ofReal]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  · rw [indicator_of_notMem hs]
    simp [b3Rest2_F, hs]

/-- **The contribution of one crossing**: on a neighbourhood `W` mapped injectively by `Φ` onto a
set containing the support of `ρ_ε`, with `J` of constant sign `σ`, the integral is `σ ∫ ρ_ε`. -/
theorem b3Rest2_integral_W {O : Set ℝ} {a b : ℝ} {d d' c c' : ℝ → ℂ}
    (hd : ∀ s ∈ O, HasDerivAt d (d' s) s) (hcd : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t)
    {W : Set ℂ} (hWo : IsOpen W) (hWsub : ∀ q ∈ W, q.re ∈ O ∧ q.im ∈ Ioo a b)
    (hinj : InjOn (fun z : ℂ ↦ d z.re - c z.im) W) {σ : ℝ}
    (hσ : ∀ q ∈ W, (conj (c' q.im) * d' q.re).im = σ * |(conj (c' q.im) * d' q.re).im|)
    {ε : ℝ} (hε : 0 < ε) (hball : ball 0 ε ⊆ (fun z : ℂ ↦ d z.re - c z.im) '' W) :
    ∫ q in W, b3Rest2_F O d d' c c' ε q = σ * ∫ z, b3Rest_rho ε z := by
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hWo.measurableSet
    (fun q hq ↦ (b3Rest2_hasFDerivAt_Φ (hd _ (hWsub q hq).1) (hcd _ (hWsub q hq).2)).hasFDerivWithinAt)
    hinj (b3Rest_rho ε)
  have hfull : ∫ x in (fun z : ℂ ↦ d z.re - c z.im) '' W, b3Rest_rho ε x =
      ∫ z, b3Rest_rho ε z := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_
    refine b3Rest_rho_eq_zero hε ?_
    by_contra hlt
    exact hz (hball (mem_ball_zero_iff.2 (not_le.1 hlt)))
  rw [← hfull, hcv, ← integral_const_mul]
  refine setIntegral_congr_fun hWo.measurableSet fun q hq ↦ ?_
  have hdet : (b3Rest2_D (d' q.re) (c' q.im)).det = (conj (c' q.im) * d' q.re).im :=
    b3Rest2_det_D _ _
  simp only [b3Rest2_F, (hWsub q hq).1, ite_true, smul_eq_mul, hdet]
  conv_lhs => rw [hσ q hq]
  ring

theorem b3Rest2_exists_sep {Z : Finset ℂ} : ∃ r > 0, ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → 2 * r < dist p q := by
  obtain ⟨r, hr, h⟩ := b3Rest_exists_pos_lt (Z.offDiag) (fun pq ↦ dist pq.1 pq.2 / 2)
    fun pq hpq ↦ by
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.1 hpq
      exact half_pos (dist_pos.2 hne)
  refine ⟨r, hr, fun p hp q hq hpq ↦ ?_⟩
  have := h (p, q) (Finset.mem_offDiag.2 ⟨hp, hq, hpq⟩)
  simp only at this
  linarith

set_option maxHeartbeats 400000 in
/-- **The local degree of a smeared arc along a transverse path.** -/
theorem b3Rest2_degree {a b s0 s1 : ℝ} (hab : a ≤ b) (hs : s0 ≤ s1)
    {O : Set ℝ} (hO : IsOpen O) {Tc : Set ℝ} (hTc : IsCompact Tc) (hTcO : Tc ⊆ O)
    (hTcI : Tc ⊆ Icc s0 s1) {d d' c c' : ℝ → ℂ}
    (hd : ∀ s ∈ O, HasDerivAt d (d' s) s) (hd' : ContinuousOn d' O)
    (hc : Continuous c) (hc' : Continuous c') (hcd : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t)
    {ε0 : ℝ} (hε0 : 0 < ε0)
    (haway : ∀ s ∈ Icc s0 s1, s ∈ O → s ∉ Tc → ∀ t ∈ Icc a b, ε0 ≤ ‖d s - c t‖)
    (hZ : {q : ℂ | q.re ∈ Tc ∧ q.im ∈ Icc a b ∧ d q.re = c q.im}.Finite)
    (hZint : ∀ q ∈ {q : ℂ | q.re ∈ Tc ∧ q.im ∈ Icc a b ∧ d q.re = c q.im},
      q.re ∈ Ioo s0 s1 ∧ q.im ∈ Ioo a b)
    (hZtr : ∀ q ∈ {q : ℂ | q.re ∈ Tc ∧ q.im ∈ Icc a b ∧ d q.re = c q.im},
      (conj (c' q.im) * d' q.re).im ≠ 0) :
    ∃ ε1 > 0, ∀ ε, 0 < ε → ε < ε1 →
      ∫ s in s0..s1, O.indicator (fun s ↦ (conj (b3Rest_arcK ε c c' a b (d s)) * d' s).im) s =
        (∫ z, b3Rest_rho ε z) * ∑ᶠ q ∈ {q : ℂ | q.re ∈ Tc ∧ q.im ∈ Icc a b ∧ d q.re = c q.im},
          (SignType.sign ((conj (c' q.im) * d' q.re).im) : ℝ) := by
  classical
  set Z := {q : ℂ | q.re ∈ Tc ∧ q.im ∈ Icc a b ∧ d q.re = c q.im}
  set Zf := hZ.toFinset
  have hZf : ∀ q, q ∈ Zf ↔ q ∈ Z := fun q ↦ hZ.mem_toFinset
  set Φ : ℂ → ℂ := fun z ↦ d z.re - c z.im
  set J : ℂ → ℝ := fun q ↦ (conj (c' q.im) * d' q.re).im
  set V := {q : ℂ | q.re ∈ O ∩ Ioo s0 s1 ∧ q.im ∈ Ioo a b}
  have hVo : IsOpen V :=
    ((hO.inter isOpen_Ioo).preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  have hdc : ContinuousOn d O := fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt
  -- continuity of the integrand on `V`
  have hFc : ∀ ε, ContinuousOn (b3Rest2_F O d d' c c' ε) V := by
    intro ε
    have h1 : ContinuousOn (fun q : ℂ ↦ b3Rest_rho ε (d q.re - c q.im) *
        (conj (c' q.im) * d' q.re).im) V := by
      refine ContinuousOn.mul ?_ ?_
      · refine (b3Rest_rho_contDiff ε).continuous.comp_continuousOn ?_
        exact (hdc.comp Complex.continuous_re.continuousOn fun q hq ↦ hq.1.1).sub
          (hc.comp Complex.continuous_im).continuousOn
      · refine Complex.continuous_im.comp_continuousOn ?_
        exact ((Complex.continuous_conj.comp (hc'.comp Complex.continuous_im)).continuousOn).mul
          (hd'.comp Complex.continuous_re.continuousOn fun q hq ↦ hq.1.1)
    exact h1.congr fun q hq ↦ by simp [b3Rest2_F, hq.1.1]
  -- separation radius and neighbourhoods of the crossings
  obtain ⟨r0, hr0, hsep⟩ := b3Rest2_exists_sep (Z := Zf)
  have hrad : ∀ p ∈ Z, ∃ r > 0, r ≤ r0 ∧ closedBall p r ⊆ V := by
    intro p hp
    have hpV : p ∈ V := ⟨⟨hTcO hp.1, (hZint p hp).1⟩, (hZint p hp).2⟩
    obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.1 hVo p hpV
    refine ⟨min r0 (R / 2), lt_min hr0 (half_pos hR), min_le_left _ _, ?_⟩
    exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hR))).trans hRV
  choose! r hr hrr0 hrV using hrad
  have hloc : ∀ p ∈ Z, ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧ W ⊆ ball p (r p) ∧
      (∀ q ∈ W, q.re ∈ O ∧ q.im ∈ Ioo a b) ∧ InjOn Φ W ∧
      (∀ q ∈ W, SignType.sign (J q) = SignType.sign (J p)) ∧ ∃ ε > 0, ball 0 ε ⊆ Φ '' W :=
    fun p hp ↦ b3Rest2_local_inv hO hd hd' hc' hcd (hTcO hp.1) (hZint p hp).2 hp.2.2
      (hZtr p hp) (hr p hp)
  choose! W hWo hpW hWb hWsub hWinj hWsign εp hεp hεpW using hloc
  -- the strip and its part away from the crossings
  set St := {q : ℂ | q.re ∈ Tc ∧ q.im ∈ Icc a b}
  have hSt : IsCompact St := by
    have : St = (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * Complex.I) '' (Tc ×ˢ Icc a b) := by
      ext q
      constructor
      · intro hq
        exact ⟨(q.re, q.im), ⟨hq.1, hq.2⟩, Complex.re_add_im q⟩
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        exact ⟨by simpa using hx1, by simpa using hx2⟩
    rw [this]
    exact (hTc.prod isCompact_Icc).image (by fun_prop)
  set M := St \ ⋃ p ∈ Zf, W p
  have hM : IsCompact M := hSt.diff (isOpen_biUnion fun p hp ↦ hWo p ((hZf p).1 hp))
  have hΦc : ContinuousOn (fun q ↦ ‖Φ q‖) M := by
    refine continuous_norm.comp_continuousOn ?_
    exact (hdc.comp Complex.continuous_re.continuousOn fun q hq ↦ hTcO hq.1.1).sub
      (hc.comp Complex.continuous_im).continuousOn
  have hΦM : ∀ q ∈ M, 0 < ‖Φ q‖ := by
    intro q hq
    refine norm_pos_iff.2 fun h0 ↦ hq.2 ?_
    have hqZ : q ∈ Z := ⟨hq.1.1, hq.1.2, sub_eq_zero.1 h0⟩
    exact mem_biUnion ((hZf q).2 hqZ) (hpW q hqZ)
  obtain ⟨η, hη, hηM⟩ : ∃ η > 0, ∀ q ∈ M, η ≤ ‖Φ q‖ := by
    rcases M.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨q₀, hq₀, hmin⟩ := hM.exists_isMinOn hne hΦc
      exact ⟨‖Φ q₀‖, hΦM q₀ hq₀, fun q hq ↦ hmin hq⟩
  obtain ⟨ε2, hε2, hε2p⟩ := b3Rest_exists_pos_lt Zf εp fun p hp ↦ hεp p ((hZf p).1 hp)
  refine ⟨min (min ε0 η) ε2, lt_min (lt_min hε0 hη) hε2, fun ε hε hεlt ↦ ?_⟩
  have hεε0 : ε < ε0 := hεlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεη : ε < η := hεlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεp' : ∀ p ∈ Zf, ε < εp p := fun p hp ↦ (hεlt.trans_le (min_le_right _ _)).trans (hε2p p hp)
  set F := b3Rest2_F O d d' c c' ε
  set R := {q : ℂ | q.re ∈ Icc s0 s1 ∧ q.im ∈ Icc a b}
  have hRm : MeasurableSet R :=
    (measurableSet_Icc.preimage Complex.measurable_re).inter
      (measurableSet_Icc.preimage Complex.measurable_im)
  have hWR : ∀ p ∈ Z, W p ⊆ R := fun p hp q hq ↦ by
    have := hrV p hp (ball_subset_closedBall (hWb p hp hq))
    exact ⟨Ioo_subset_Icc_self this.1.2, Ioo_subset_Icc_self this.2⟩
  -- the integrand is supported in the neighbourhoods of the crossings
  have hsupp : ∀ q ∈ R, F q ≠ 0 → ∃ p ∈ Zf, q ∈ W p := by
    intro q hqR hF
    have hqO : q.re ∈ O := by
      by_contra h
      exact hF (by simp [F, b3Rest2_F, h])
    have hρ : b3Rest_rho ε (Φ q) ≠ 0 := by
      intro h0
      exact hF (by simp [F, b3Rest2_F, hqO, Φ] at h0 ⊢; simp [h0])
    have hlt : ‖Φ q‖ < ε := by
      by_contra hge
      exact hρ (b3Rest_rho_eq_zero hε (not_lt.1 hge))
    have hqT : q.re ∈ Tc := by
      by_contra hT
      have := haway q.re hqR.1 hqO hT q.im hqR.2
      linarith
    by_contra hnot
    push_neg at hnot
    have hqM : q ∈ M := ⟨⟨hqT, hqR.2⟩, by
      simp only [mem_iUnion]
      rintro ⟨p, hp, hqp⟩
      exact hnot p hp hqp⟩
    have := hηM q hqM
    linarith
  have hdisj : ∀ p ∈ Zf, ∀ p' ∈ Zf, p ≠ p' → ∀ q ∈ W p, q ∉ W p' := by
    intro p hp p' hp' hne q hq hq'
    have h1 := mem_ball.1 (hWb p ((hZf p).1 hp) hq)
    have h2 := mem_ball.1 (hWb p' ((hZf p').1 hp') hq')
    have h3 := hsep p hp p' hp' hne
    have := dist_triangle_left p p' q
    have h4 := hrr0 p ((hZf p).1 hp)
    have h5 := hrr0 p' ((hZf p').1 hp')
    linarith
  have hsum : ∀ q ∈ R, F q = ∑ p ∈ Zf, (W p).indicator F q := by
    intro q hqR
    by_cases hF : F q = 0
    · rw [hF]
      exact (Finset.sum_eq_zero fun p _ ↦ by simp [indicator, hF]).symm
    · obtain ⟨p, hp, hqp⟩ := hsupp q hqR hF
      rw [Finset.sum_eq_single p (fun p' hp' hne ↦ indicator_of_notMem
        (hdisj p hp p' hp' (Ne.symm hne) q hqp) F) (fun h ↦ absurd hp h), indicator_of_mem hqp]
  have hintW : ∀ p ∈ Z, IntegrableOn F (W p) := fun p hp ↦
    ((hFc ε).mono (hrV p hp)).integrableOn_compact (isCompact_closedBall p (r p)) |>.mono_set
      (fun q hq ↦ ball_subset_closedBall (hWb p hp hq))
  have hintR : IntegrableOn F R := by
    have : IntegrableOn (fun q ↦ ∑ p ∈ Zf, (W p).indicator F q) R :=
      (integrable_finset_sum _ fun p hp ↦
        (integrable_indicator_iff (hWo p ((hZf p).1 hp)).measurableSet).2
          (hintW p ((hZf p).1 hp))).integrableOn
    exact this.congr_fun (fun q hq ↦ (hsum q hq).symm) hRm
  rw [intervalIntegral.integral_congr (g := fun s ↦ ∫ t in a..b, F ⟨s, t⟩)
    (fun s _ ↦ b3Rest2_inner_eq O hc hc' ε a b s), b3Rest2_iterated_eq hs hab hintR,
    setIntegral_congr_fun hRm hsum, integral_finset_sum _ fun p hp ↦
      ((integrable_indicator_iff (hWo p ((hZf p).1 hp)).measurableSet).2
        (hintW p ((hZf p).1 hp))).integrableOn,
    finsum_mem_eq_finite_toFinset_sum _ hZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpZ := (hZf p).1 hp
  rw [setIntegral_indicator (hWo p hpZ).measurableSet, inter_eq_right.2 (hWR p hpZ)]
  rw [b3Rest2_integral_W hd hcd (hWo p hpZ) (hWsub p hpZ) (hWinj p hpZ) (σ := SignType.sign (J p))
    (fun q hq ↦ ?_) hε ((ball_subset_ball (hεp' p hp).le).trans (hεpW p hpZ)), mul_comm]
  have hs := hWsign p hpZ q hq
  have hne : J q ≠ 0 := by
    intro h0
    rw [show J q = 0 from h0, sign_zero] at hs
    exact hZtr p hpZ (sign_eq_zero_iff.1 hs.symm)
  show J q = (SignType.sign (J p) : ℝ) * |J q|
  rw [← hs]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [sign_neg h, abs_of_neg h]; simp
  · rw [sign_pos h, abs_of_pos h]; simp

end HodgeLean.Foundations.Program
