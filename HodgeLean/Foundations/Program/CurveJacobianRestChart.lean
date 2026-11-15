import HodgeLean.Foundations.Program.CurveJacobianRestL2
import HodgeLean.Foundations.Program.CurveJacobianFormsHarmonic

/-! # Track B3, lane Rest: the `L²` pairing in a chart disc

In the complex coordinate `z ↦ φ_q(q) + z e` of the chart at `q`, a real `1`-form `α` has the
complex coefficient `u_α = α(e) - i α(i e)` (`b3Rest_coef`). For a form `φ` supported in the image
of the disc `|z| < r`, the pairing `∫ α ∧ ⋆φ` is `∫_{|z| < r} Re (u_α · conj u_φ) dz`
(`b3Rest_inner_eq_disc`): the density of `α ∧ ⋆φ` on the basis `(e, i e)` is
`α(e) φ(e) + α(i e) φ(i e)`, and the Haar measure of the basis `(e, i e)` is the image of the
Lebesgue measure of `ℂ` under `z ↦ z e`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The real-linear coordinate `ℂ ≃ E`, `z ↦ z e`. -/
def b3Rest_L (hE : Module.finrank ℂ E = 1) : ℂ ≃L[ℝ] E where
  toLinearEquiv := (b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).continuous
  continuous_invFun := (b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).symm.continuous

theorem b3Rest_L_apply (hE : Module.finrank ℂ E = 1) (z : ℂ) : b3Rest_L hE z = z • b3Rest_e hE :=
  rfl

theorem b3Rest_b_eq_map (hE : Module.finrank ℂ E = 1) :
    b3Rest_b hE = Complex.basisOneI.map (b3Rest_L hE).toLinearEquiv := by
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  fin_cases i
  · simp [b3Rest_b, b3Forms_cplxBasis_zero, b3Rest_L_apply]
  · simp [b3Rest_b, b3Forms_cplxBasis_one, b3Rest_L_apply]

variable [MeasurableSpace E] [BorelSpace E]

theorem b3Rest_basisOneI_addHaar : Complex.basisOneI.addHaar = (volume : Measure ℂ) := by
  rw [Module.Basis.addHaar_eq_iff]
  have := Complex.orthonormalBasisOneI.volume_parallelepiped
  simpa using this

/-- **Integrals for the Haar measure of `(e, i e)`** in the coordinate `z ↦ c + z e`. -/
theorem b3Rest_integral_addHaar_eq (hE : Module.finrank ℂ E = 1) (f : E → ℝ) (c : E) :
    ∫ u, f u ∂(b3Rest_b hE).addHaar = ∫ z : ℂ, f (c + z • b3Rest_e hE) := by
  rw [← integral_add_left_eq_self (μ := (b3Rest_b hE).addHaar) _ c]
  have hmap : (b3Rest_b hE).addHaar = Measure.map (b3Rest_L hE) volume := by
    rw [b3Rest_b_eq_map, ← Module.Basis.map_addHaar, b3Rest_basisOneI_addHaar]
  rw [hmap]
  have hme : MeasurableEmbedding (b3Rest_L hE) := (b3Rest_L hE).toHomeomorph.measurableEmbedding
  rw [hme.integral_map]
  rfl

/-! ## Coefficients in a chart disc -/

attribute [local instance] b3Forms_isManifold_real

/-- The point `φ_q(q) + z e` of the chart image at `q`. -/
def b3Rest_ζ (hE : Module.finrank ℂ E = 1) (q : C) (z : ℂ) : E := chartAt E q q + z • b3Rest_e hE

/-- **The complex coefficient** `α(e) - i α(i e)` of a real `1`-form in the chart disc at `q`. -/
def b3Rest_coef (hE : Module.finrank ℂ E = 1) (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (q : C) (z : ℂ) : ℂ :=
  (b3Forms_loc α q (b3Rest_ζ hE q z) (fun _ ↦ b3Rest_e hE) : ℂ) -
    Complex.I * (b3Forms_loc α q (b3Rest_ζ hE q z) (fun _ ↦ Complex.I • b3Rest_e hE) : ℂ)

/-- The image of the disc `|z| < r` in the chart domain at `q`. -/
def b3Rest_reg (hE : Module.finrank ℂ E = 1) (q : C) (r : ℝ) : Set C :=
  (chartAt E q).source ∩ chartAt E q ⁻¹' (b3Rest_ζ hE q '' ball 0 r)

theorem b3Rest_ζ_injective (hE : Module.finrank ℂ E = 1) (q : C) :
    Function.Injective (b3Rest_ζ hE q) := by
  intro z w h
  simp only [b3Rest_ζ, add_right_inj] at h
  exact smul_left_injective ℂ (b3Rest_e_ne_zero hE) h

theorem b3Rest_re_coef_mul_conj (hE : Module.finrank ℂ E = 1) (α φ : C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (q : C) (z : ℂ) :
    (b3Rest_coef hE α q z * starRingEnd ℂ (b3Rest_coef hE φ q z)).re =
      b3Forms_loc α q (b3Rest_ζ hE q z) (fun _ ↦ b3Rest_e hE) *
          b3Forms_loc φ q (b3Rest_ζ hE q z) (fun _ ↦ b3Rest_e hE) +
        b3Forms_loc α q (b3Rest_ζ hE q z) (fun _ ↦ Complex.I • b3Rest_e hE) *
          b3Forms_loc φ q (b3Rest_ζ hE q z) (fun _ ↦ Complex.I • b3Rest_e hE) := by
  simp only [b3Rest_coef, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  ring

theorem b3Rest_starPt_zero : b3Forms_starPt (0 : E [⋀^Fin 1]→L[ℝ] ℝ) = 0 := by
  ext v
  simp [b3Forms_starPt]

theorem b3Rest_wedge_zero_right (a : E [⋀^Fin 1]→L[ℝ] ℝ) : b3Forms_wedge a 0 = 0 := by
  have := b3Forms_wedge_smul_right 0 a 0
  rw [zero_smul, zero_smul] at this
  exact this

theorem b3Rest_wedge_star_eq_zero {α φ : C → E [⋀^Fin 1]→L[ℝ] ℝ} {p : C} (h : φ p = 0) :
    b3Forms_wedgeForm α (b3Forms_star φ) p = 0 := by
  simp only [b3Forms_wedgeForm, b3Forms_star, h, b3Rest_starPt_zero, b3Rest_wedge_zero_right]

variable [T2Space C] [CompactSpace C]

/-- **The pairing of two forms in a chart disc**: if `φ` is supported in the image of `|z| < r`
(inside the chart), `∫ α ∧ ⋆φ = ∫_{|z| < r} Re (u_α · conj u_φ)`. -/
theorem b3Rest_inner_eq_disc (hE : Module.finrank ℂ E = 1) {α φ : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (hφ : b3Forms_IsSmooth φ) (q : C) {r : ℝ}
    (hr : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ hE q z ∈ (chartAt E q).target)
    (hsupp : tsupport φ ⊆ b3Rest_reg hE q r) :
    b3Rest_inner hE α φ =
      ∫ z in ball (0 : ℂ) r, (b3Rest_coef hE α q z * starRingEnd ℂ (b3Rest_coef hE φ q z)).re := by
  have hω : b3Forms_IsSmooth (b3Forms_wedgeForm α (b3Forms_star φ)) := hα.wedgeForm hφ.star
  have htsupp : tsupport (b3Forms_wedgeForm α (b3Forms_star φ)) ⊆ (chartAt E q).source := by
    refine (closure_mono fun p hp ↦ ?_).trans (hsupp.trans inter_subset_left)
    by_contra h0
    exact hp (b3Rest_wedge_star_eq_zero (Function.notMem_support.1 h0))
  rw [b3Rest_inner, b3Forms_integral_eq_chartIntegral _ b3Forms_oriented_complex hω htsupp,
    b3Forms_chartIntegral, b3Rest_integral_addHaar_eq hE _ (chartAt E q q),
    ← integral_indicator measurableSet_ball]
  congr 1
  funext z
  change b3Forms_chartFun (b3Rest_b hE) q _ (b3Rest_ζ hE q z) = _
  by_cases hz : z ∈ ball (0 : ℂ) r
  · rw [indicator_of_mem hz, b3Forms_chartFun, indicator_of_mem (hr z (mem_ball_zero_iff.1 hz)),
      b3Forms_loc_wedgeForm, b3Rest_re_coef_mul_conj]
    show b3Forms_wedge _ _ _ = _
    rw [b3Forms_loc_star φ (hr z (mem_ball_zero_iff.1 hz)), b3Forms_wedge_starPt_basis]
  · rw [indicator_of_notMem hz, b3Forms_chartFun]
    by_cases ht : b3Rest_ζ hE q z ∈ (chartAt E q).target
    · rw [indicator_of_mem ht]
      have hnot : (chartAt E q).symm (b3Rest_ζ hE q z) ∉ tsupport φ := by
        intro hmem
        obtain ⟨-, w, hw, hw'⟩ := hsupp hmem
        rw [(chartAt E q).right_inv ht] at hw'
        exact hz (b3Rest_ζ_injective hE q hw' ▸ hw)
      have h0 : φ ((chartAt E q).symm (b3Rest_ζ hE q z)) = 0 := image_eq_zero_of_notMem_tsupport hnot
      have : b3Forms_loc (b3Forms_wedgeForm α (b3Forms_star φ)) q (b3Rest_ζ hE q z) = 0 := by
        simp only [b3Forms_loc, b3Rest_wedge_star_eq_zero h0]
        ext v
        simp
      rw [this]
      rfl
    · rw [indicator_of_notMem ht]

/-! ## Functions from the chart disc -/

section ChartFun

omit [MeasurableSpace E] [BorelSpace E] [T2Space C] [CompactSpace C]

theorem b3Rest_L_symm_ζ (hE : Module.finrank ℂ E = 1) (q : C) (z : ℂ) :
    (b3Rest_L hE).symm (b3Rest_ζ hE q z - chartAt E q q) = z := by
  rw [b3Rest_ζ, add_sub_cancel_left, ← b3Rest_L_apply, ContinuousLinearEquiv.symm_apply_apply]

open scoped Classical in
/-- **The function on `C` given by `g` in the chart disc at `q`**, extended by `0`. -/
def b3Rest_cfun (hE : Module.finrank ℂ E = 1) (q : C) (g : ℂ → ℝ) : C → ℝ := fun p ↦
  if p ∈ (chartAt E q).source then g ((b3Rest_L hE).symm (chartAt E q p - chartAt E q q)) else 0

theorem b3Rest_cfun_symm (hE : Module.finrank ℂ E = 1) (q : C) (g : ℂ → ℝ) {u : E}
    (hu : u ∈ (chartAt E q).target) :
    b3Rest_cfun hE q g ((chartAt E q).symm u) = g ((b3Rest_L hE).symm (u - chartAt E q q)) := by
  simp [b3Rest_cfun, (chartAt E q).map_target hu, (chartAt E q).right_inv hu]

/-- The chart function is a chart-local `0`-form. -/
theorem b3Rest_fun_cfun (hE : Module.finrank ℂ E = 1) (q : C) (g : ℂ → ℝ) :
    b3Forms_fun (E := E) (b3Rest_cfun hE q g) =
      b3Rest_ofLoc q (fun u ↦ constOfIsEmpty ℝ E (Fin 0)
        (g ((b3Rest_L hE).symm (u - chartAt E q q)))) := by
  funext p
  by_cases hp : p ∈ (chartAt E q).source
  · simp only [b3Forms_fun, b3Rest_cfun, b3Rest_ofLoc, hp, ite_true]
    ext v
    simp
  · simp only [b3Forms_fun, b3Rest_cfun, b3Rest_ofLoc, hp, ite_false]
    ext v
    simp

/-- **Chart functions of compactly supported smooth functions are smooth.** -/
theorem b3Rest_smoothFun_cfun (hE : Module.finrank ℂ E = 1) (q : C) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : ∀ z ∈ tsupport g, b3Rest_ζ hE q z ∈ (chartAt E q).target) [T2Space C] :
    b3Rest_SmoothFun (E := E) (b3Rest_cfun hE q g) := by
  unfold b3Rest_SmoothFun
  rw [b3Rest_fun_cfun]
  set ψ : E → ℂ := fun u ↦ (b3Rest_L hE).symm (u - chartAt E q q)
  have hψ : ContDiff ℝ ∞ ψ :=
    (b3Rest_L hE).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hA : ContDiff ℝ ∞ (fun u ↦ constOfIsEmpty ℝ E (Fin 0) (g (ψ u))) :=
    (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).toContinuousLinearEquiv.contDiff.comp (hg.comp hψ)
  have hts : tsupport (fun u ↦ constOfIsEmpty ℝ E (Fin 0) (g (ψ u))) ⊆
      (fun z ↦ b3Rest_ζ hE q z) '' tsupport g := by
    have hhom : (fun z ↦ b3Rest_ζ hE q z) = fun z ↦ chartAt E q q + b3Rest_L hE z := by
      funext z; rfl
    refine closure_minimal (fun u hu ↦ ?_) ?_
    · have hne : g (ψ u) ≠ 0 := by
        intro h0; apply hu
        show constOfIsEmpty ℝ E (Fin 0) (g (ψ u)) = 0
        rw [h0]
        ext v
        simp
      refine ⟨ψ u, subset_closure hne, ?_⟩
      show chartAt E q q + ψ u • b3Rest_e hE = u
      rw [← b3Rest_L_apply, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    · rw [hhom]
      exact (hgc.isCompact.image (continuous_const.add (b3Rest_L hE).continuous)).isClosed
  have himc : IsCompact ((fun z ↦ b3Rest_ζ hE q z) '' tsupport g) := by
    have hc : Continuous fun z ↦ b3Rest_ζ hE q z := by
      show Continuous fun z : ℂ ↦ chartAt E q q + z • b3Rest_e hE
      fun_prop
    exact hgc.isCompact.image hc
  refine b3Rest_isSmooth_ofLoc q hA (himc.of_isClosed_subset (isClosed_tsupport _) hts)
    (hts.trans ?_)
  · rintro _ ⟨z, hz, rfl⟩
    exact hgs z hz

end ChartFun

/-! ## Coefficients of `d`, `⋆` and products -/

section CoefFormulas

omit [MeasurableSpace E] [BorelSpace E] [T2Space C] [CompactSpace C]

/-- The coefficient of `⋆β` is `-i` times that of `β`. -/
theorem b3Rest_coef_star (hE : Module.finrank ℂ E = 1) (β : C → E [⋀^Fin 1]→L[ℝ] ℝ) (q : C)
    {z : ℂ} (hz : b3Rest_ζ hE q z ∈ (chartAt E q).target) :
    b3Rest_coef hE (b3Forms_star β) q z = -Complex.I * b3Rest_coef hE β q z := by
  simp only [b3Rest_coef, b3Forms_loc_star β hz, b3Forms_starPt_apply, smul_smul,
    Complex.I_mul_I, neg_one_smul, b3Forms_apply_neg_const]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The coefficient of `h β` is `h` times that of `β`. -/
theorem b3Rest_coef_smulFun (hE : Module.finrank ℂ E = 1) (h : C → ℝ)
    (β : C → E [⋀^Fin 1]→L[ℝ] ℝ) (q : C) (z : ℂ) :
    b3Rest_coef hE (b3Forms_smulFun h β) q z =
      (h ((chartAt E q).symm (b3Rest_ζ hE q z)) : ℂ) * b3Rest_coef hE β q z := by
  simp only [b3Rest_coef, b3Forms_loc_smulFun, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **The coefficient of the differential of a chart function**: `g_x - i g_y`. -/
theorem b3Rest_coef_d_cfun (hE : Module.finrank ℂ E = 1) (q : C) {g : ℂ → ℝ}
    (hgd : Differentiable ℝ g)
    (hsm : b3Rest_SmoothFun (E := E) (b3Rest_cfun hE q g)) {z : ℂ}
    (hz : b3Rest_ζ hE q z ∈ (chartAt E q).target) :
    b3Rest_coef hE (b3Forms_d (b3Forms_fun (E := E) (b3Rest_cfun hE q g))) q z =
      (fderiv ℝ g z 1 : ℂ) - Complex.I * (fderiv ℝ g z Complex.I : ℂ) := by
  set ψ : E → ℂ := fun u ↦ (b3Rest_L hE).symm (u - chartAt E q q)
  have hev : (b3Rest_cfun hE q g) ∘ (chartAt E q).symm =ᶠ[𝓝 (b3Rest_ζ hE q z)] g ∘ ψ := by
    filter_upwards [(chartAt E q).open_target.mem_nhds hz] with u hu
    exact b3Rest_cfun_symm hE q g hu
  have hψd : HasFDerivAt ψ ((b3Rest_L hE).symm : E →L[ℝ] ℂ) (b3Rest_ζ hE q z) := by
    have h := ((b3Rest_L hE).symm : E →L[ℝ] ℂ).hasFDerivAt.comp (b3Rest_ζ hE q z)
      ((hasFDerivAt_id _).sub_const (chartAt E q q))
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hψz : ψ (b3Rest_ζ hE q z) = z := b3Rest_L_symm_ζ hE q z
  have hfd : fderiv ℝ ((b3Rest_cfun hE q g) ∘ (chartAt E q).symm) (b3Rest_ζ hE q z) =
      (fderiv ℝ g z).comp ((b3Rest_L hE).symm : E →L[ℝ] ℂ) := by
    rw [hev.fderiv_eq]
    have := (hgd (ψ (b3Rest_ζ hE q z))).hasFDerivAt.comp (b3Rest_ζ hE q z) hψd
    rw [hψz] at this
    exact this.fderiv
  have hloc : ∀ v : E, b3Forms_loc (b3Forms_d (b3Forms_fun (E := E) (b3Rest_cfun hE q g))) q
      (b3Rest_ζ hE q z) (fun _ ↦ v) = fderiv ℝ g z ((b3Rest_L hE).symm v) := by
    intro v
    rw [b3Forms_loc_d hsm q hz, b3Forms_loc_fun]
    have := extDeriv_constOfIsEmpty (𝕜 := ℝ)
      (fun u ↦ b3Rest_cfun hE q g ((chartAt E q).symm u)) (b3Rest_ζ hE q z)
    rw [this, show (fun x ↦ b3Rest_cfun hE q g ((chartAt E q).symm x)) =
      (b3Rest_cfun hE q g) ∘ (chartAt E q).symm from rfl, hfd]
    simp
  have he : (b3Rest_L hE).symm (b3Rest_e hE) = 1 := by
    rw [ContinuousLinearEquiv.symm_apply_eq, b3Rest_L_apply, one_smul]
  have hie : (b3Rest_L hE).symm (Complex.I • b3Rest_e hE) = Complex.I := by
    rw [ContinuousLinearEquiv.symm_apply_eq, b3Rest_L_apply]
  simp only [b3Rest_coef, hloc, he, hie]

end CoefFormulas

/-! ## Cutoffs and the local `L²` bound -/

section Cutoff

omit [MeasurableSpace E] [BorelSpace E] [CompactSpace C]

/-- A smooth bump on `ℂ`, equal to `1` on `|z| ≤ r₁` and supported in `|z| < r₂`. -/
theorem b3Rest_exists_bump {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ ball 0 r₂ ∧
      (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧ ∀ z ∈ closedBall (0 : ℂ) r₁, g z = 1 := by
  let f : ContDiffBump (0 : ℂ) := ⟨r₁, (r₁ + r₂) / 2, h1, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, fun z ↦ ⟨f.nonneg, f.le_one⟩,
    fun z hz ↦ f.one_of_mem_closedBall hz⟩
  rw [f.tsupport_eq]
  exact closedBall_subset_ball (by show (r₁ + r₂) / 2 < r₂; linarith)

theorem b3Rest_cfun_nonneg (hE : Module.finrank ℂ E = 1) (q : C) {g : ℂ → ℝ}
    (hg : ∀ z, 0 ≤ g z ∧ g z ≤ 1) (p : C) :
    0 ≤ b3Rest_cfun hE q g p ∧ b3Rest_cfun hE q g p ≤ 1 := by
  unfold b3Rest_cfun
  split_ifs
  · exact hg _
  · exact ⟨le_rfl, zero_le_one⟩

theorem b3Rest_cfun_ζ (hE : Module.finrank ℂ E = 1) (q : C) (g : ℂ → ℝ) {z : ℂ}
    (hz : b3Rest_ζ hE q z ∈ (chartAt E q).target) :
    b3Rest_cfun hE q g ((chartAt E q).symm (b3Rest_ζ hE q z)) = g z := by
  rw [b3Rest_cfun_symm hE q g hz, b3Rest_L_symm_ζ]

/-- The support of a chart function lies over the support of `g`. -/
theorem b3Rest_tsupport_cfun (hE : Module.finrank ℂ E = 1) (q : C) {g : ℂ → ℝ}
    (hgc : HasCompactSupport g)
    (hgs : ∀ z ∈ tsupport g, b3Rest_ζ hE q z ∈ (chartAt E q).target) :
    tsupport (b3Rest_cfun hE q g) ⊆
      (chartAt E q).symm '' (b3Rest_ζ hE q '' tsupport g) := by
  have hζc : Continuous (b3Rest_ζ hE q) := by
    show Continuous fun z : ℂ ↦ chartAt E q q + z • b3Rest_e hE
    fun_prop
  have hK : IsCompact ((chartAt E q).symm '' (b3Rest_ζ hE q '' tsupport g)) :=
    (hgc.isCompact.image hζc).image_of_continuousOn
      ((chartAt E q).continuousOn_symm.mono fun u ⟨z, hz, hzu⟩ ↦ hzu ▸ hgs z hz)
  refine closure_minimal (fun p hp ↦ ?_) hK.isClosed
  have hps : p ∈ (chartAt E q).source := by
    by_contra h
    exact hp (by simp [b3Rest_cfun, h])
  set z := (b3Rest_L hE).symm (chartAt E q p - chartAt E q q)
  have hgz : g z ≠ 0 := by
    intro h0
    apply hp
    show b3Rest_cfun hE q g p = 0
    simp only [b3Rest_cfun, hps, ite_true]
    exact h0
  have hζz : b3Rest_ζ hE q z = chartAt E q p := by
    show chartAt E q q + z • b3Rest_e hE = _
    rw [← b3Rest_L_apply, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  refine ⟨b3Rest_ζ hE q z, ⟨z, subset_closure hgz, rfl⟩, ?_⟩
  rw [hζz]
  exact (chartAt E q).left_inv hps

theorem b3Rest_tsupport_cfun_reg (hE : Module.finrank ℂ E = 1) (q : C) {g : ℂ → ℝ} {r : ℝ}
    (hgc : HasCompactSupport g) (hgr : tsupport g ⊆ ball 0 r)
    (hr : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ hE q z ∈ (chartAt E q).target) :
    tsupport (b3Rest_cfun hE q g) ⊆ b3Rest_reg hE q r := by
  have hgs : ∀ z ∈ tsupport g, b3Rest_ζ hE q z ∈ (chartAt E q).target := fun z hz ↦
    hr z (mem_ball_zero_iff.1 (hgr hz))
  refine (b3Rest_tsupport_cfun hE q hgc hgs).trans ?_
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨(chartAt E q).map_target (hgs z hz), z, hgr hz, ?_⟩
  exact ((chartAt E q).right_inv (hgs z hz)).symm

end Cutoff

/-! ## The local `L²` bound -/

section Bound

omit [MeasurableSpace E] [BorelSpace E] [T2Space C] [CompactSpace C] in
theorem b3Rest_continuousAt_coef (hE : Module.finrank ℂ E = 1) {α : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (q : C) {z : ℂ} (hz : b3Rest_ζ hE q z ∈ (chartAt E q).target) :
    ContinuousAt (b3Rest_coef hE α q) z := by
  have hζc : Continuous (b3Rest_ζ hE q) := by
    show Continuous fun z : ℂ ↦ chartAt E q q + z • b3Rest_e hE
    fun_prop
  have hl : ContinuousAt (b3Forms_loc α q) (b3Rest_ζ hE q z) :=
    ((hα q).continuousOn).continuousAt ((chartAt E q).open_target.mem_nhds hz)
  have hlz : ContinuousAt (fun w ↦ b3Forms_loc α q (b3Rest_ζ hE q w)) z :=
    hl.comp hζc.continuousAt
  have hev : ∀ v : Fin 1 → E, ContinuousAt (fun w ↦ b3Forms_loc α q (b3Rest_ζ hE q w) v) z :=
    fun v ↦ (continuous_eval_const v).continuousAt.comp hlz
  unfold b3Rest_coef
  exact (Complex.continuous_ofReal.continuousAt.comp (hev _)).sub
    (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp (hev _)))

theorem b3Rest_starPt_smul (c : ℝ) (A : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_starPt (c • A) = c • b3Forms_starPt A := by
  ext v
  simp [b3Forms_starPt]

theorem b3Rest_wedgeForm_star_smulFun (h : C → ℝ) (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedgeForm α (b3Forms_star (b3Forms_smulFun h β)) =
      b3Forms_smulFun h (b3Forms_wedgeForm α (b3Forms_star β)) := by
  funext p
  simp only [b3Forms_wedgeForm, b3Forms_star, b3Forms_smulFun]
  rw [b3Rest_starPt_smul, b3Forms_wedge_smul_right]

/-- **The local `L²` bound**: on a smaller disc, the coefficient of a smooth form is controlled
by its `L²` norm. -/
theorem b3Rest_integral_coef_sq_le (hE : Module.finrank ℂ E = 1) {α : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (q : C) {r' r : ℝ} (hr' : 0 < r') (hrr : r' < r)
    (hr : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ hE q z ∈ (chartAt E q).target) :
    ∫ z in ball (0 : ℂ) r', ‖b3Rest_coef hE α q z‖ ^ 2 ≤ b3Rest_inner hE α α := by
  obtain ⟨g, hg, hgc, hgr, hg01, hg1⟩ := b3Rest_exists_bump hr' hrr
  have hgs : ∀ z ∈ tsupport g, b3Rest_ζ hE q z ∈ (chartAt E q).target := fun z hz ↦
    hr z (mem_ball_zero_iff.1 (hgr hz))
  set χ := b3Rest_cfun hE q g
  have hχ : b3Rest_SmoothFun (E := E) χ := b3Rest_smoothFun_cfun hE q hg hgc hgs
  have h1χ : b3Rest_SmoothFun (E := E) (fun p ↦ 1 - χ p) := by
    have hconst : b3Rest_SmoothFun (E := E) (fun _ : C ↦ (1 : ℝ)) :=
      b3Forms_isSmooth_fun contMDiff_const
    have := hconst.add (hχ.smul (-1))
    have e : b3Forms_fun (E := E) (fun p ↦ 1 - χ p) =
        b3Forms_fun (fun _ ↦ (1 : ℝ)) + (-1 : ℝ) • b3Forms_fun χ := by
      funext p
      ext v
      simp [b3Forms_fun, sub_eq_add_neg]
    show b3Forms_IsSmooth _
    rw [e]
    exact this
  have hφ1 : b3Forms_IsSmooth (b3Forms_smulFun χ α) := b3Forms_IsSmooth.smulFun' hχ hα
  have hφ2 : b3Forms_IsSmooth (b3Forms_smulFun (fun p ↦ 1 - χ p) α) :=
    b3Forms_IsSmooth.smulFun' h1χ hα
  have hsplit : α = b3Forms_smulFun χ α + b3Forms_smulFun (fun p ↦ 1 - χ p) α := by
    funext p
    simp only [b3Forms_smulFun, Pi.add_apply]
    rw [← add_smul, add_sub_cancel, one_smul]
  have hinner : b3Rest_inner hE α α = b3Rest_inner hE α (b3Forms_smulFun χ α) +
      b3Rest_inner hE α (b3Forms_smulFun (fun p ↦ 1 - χ p) α) := by
    have h := b3Rest_inner_add_left hE hφ1 hφ2 hα
    rw [← hsplit] at h
    rw [h, b3Rest_inner_comm hE _ α, b3Rest_inner_comm hE _ α]
  -- the second part is nonnegative
  have hnn : 0 ≤ b3Rest_inner hE α (b3Forms_smulFun (fun p ↦ 1 - χ p) α) := by
    rw [b3Rest_inner, b3Rest_wedgeForm_star_smulFun]
    refine b3Forms_integral_nonneg _ fun x u hu ↦ ?_
    rw [b3Forms_loc_smulFun]
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [b3Forms_density_wedge_star hE (b3Rest_e_ne_zero hE) α hu]
    have := (b3Rest_cfun_nonneg hE q hg01 ((chartAt E x).symm u)).2
    exact mul_nonneg (by linarith) (by positivity)
  -- the first part is the disc integral
  have hreg : tsupport (b3Forms_smulFun χ α) ⊆ b3Rest_reg hE q r :=
    (b3Forms_tsupport_smulFun_subset_left _ _).trans
      (b3Rest_tsupport_cfun_reg hE q hgc hgr hr)
  have hdisc := b3Rest_inner_eq_disc hE hα hφ1 q hr hreg
  have hpt : ∀ z ∈ ball (0 : ℂ) r, (b3Rest_coef hE α q z *
      starRingEnd ℂ (b3Rest_coef hE (b3Forms_smulFun χ α) q z)).re =
        g z * ‖b3Rest_coef hE α q z‖ ^ 2 := by
    intro z hz
    have hχz : χ ((chartAt E q).symm (b3Rest_ζ hE q z)) = g z :=
      b3Rest_cfun_ζ hE q g (hr z (mem_ball_zero_iff.1 hz))
    rw [b3Rest_coef_smulFun, hχz, map_mul,
      Complex.conj_ofReal, mul_left_comm, Complex.mul_conj, Complex.re_ofReal_mul,
      Complex.normSq_eq_norm_sq]
    norm_cast
  rw [setIntegral_congr_fun measurableSet_ball hpt] at hdisc
  have hint : IntegrableOn (fun z ↦ g z * ‖b3Rest_coef hE α q z‖ ^ 2) (ball (0 : ℂ) r) := by
    have hK : IntegrableOn (fun z ↦ g z * ‖b3Rest_coef hE α q z‖ ^ 2) (tsupport g) := by
      refine ContinuousOn.integrableOn_compact hgc.isCompact fun z hz ↦ ?_
      exact (hg.continuous.continuousAt.mul
        ((b3Rest_continuousAt_coef hE hα q (hgs z hz)).norm.pow 2)).continuousWithinAt
    refine hK.of_forall_sdiff_eq_zero measurableSet_ball fun z hz ↦ ?_
    rw [image_eq_zero_of_notMem_tsupport hz.2, zero_mul]
  have hmono : ∫ z in ball (0 : ℂ) r', ‖b3Rest_coef hE α q z‖ ^ 2 ≤
      ∫ z in ball (0 : ℂ) r, g z * ‖b3Rest_coef hE α q z‖ ^ 2 := by
    have heq : ∫ z in ball (0 : ℂ) r', ‖b3Rest_coef hE α q z‖ ^ 2 =
        ∫ z in ball (0 : ℂ) r', g z * ‖b3Rest_coef hE α q z‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_ball (fun z hz ↦ by
        simp only [hg1 z (ball_subset_closedBall hz), one_mul])
    rw [heq]
    exact setIntegral_mono_set hint (Eventually.of_forall fun z ↦
      mul_nonneg (hg01 z).1 (by positivity)) (Eventually.of_forall (ball_subset_ball hrr.le))
  linarith

end Bound

end HodgeLean.Foundations.Program
