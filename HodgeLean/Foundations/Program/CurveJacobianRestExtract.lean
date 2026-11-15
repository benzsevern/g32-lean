import HodgeLean.Foundations.Program.CurveJacobianRestChart
import HodgeLean.Foundations.Program.CurveJacobianRestWeyl

/-! # Track B3, lane Rest: local coefficients of `L²` forms

Fix a chart disc `|z| < r'` at `q` (inside a larger disc of the chart). Restricting chart
coefficients to the disc is a bounded linear map `b3Rest_restr` from smooth forms to
`L²(|z| < r'; ℂ)` (`b3Rest_integral_coef_sq_le`), so it extends to the completion
(`b3Rest_restrL2`). For a form `φ` supported in the disc, `⟨h, φ⟩ = Re ⟪R h, R φ⟫`.

For a weakly harmonic `h` (orthogonal to `d C^∞` and `⋆d C^∞`) the coefficient `u = R h`
satisfies `∫ u ∂̄ψ = 0` for every test function of the disc: `∂̄ψ` is the conjugate of the
coefficient of `dψ`, and that of `⋆dψ` is `-i` times it. By Weyl's lemma it is then a holomorphic
function `G` on the half disc (`b3Rest_local_weyl`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff ComplexConjugate

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]
  [hE1 : Fact (Module.finrank ℂ E = 1)]

attribute [local instance] b3Forms_isManifold_real

/-- The data of a chart disc: radii `0 < r' < r` with the disc of radius `r` in the chart. -/
structure b3Rest_Disc (C : Type) [TopologicalSpace C] [ChartedSpace E C] where
  q : C
  r : ℝ
  r' : ℝ
  pos : 0 < r'
  lt : r' < r
  mem : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ hE1.out q z ∈ (chartAt E q).target

namespace b3Rest_Disc

variable (D : b3Rest_Disc (E := E) C)

/-- The measure of the small disc. -/
abbrev μ : Measure ℂ := volume.restrict (ball 0 D.r')

instance : IsFiniteMeasure D.μ := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

theorem mem' {z : ℂ} (hz : ‖z‖ < D.r') : b3Rest_ζ hE1.out D.q z ∈ (chartAt E D.q).target :=
  D.mem z (hz.trans D.lt)

theorem memLp_coef (α : b3Rest_SF E C) :
    MemLp (b3Rest_coef hE1.out α.form D.q) 2 D.μ := by
  have hK : IsCompact (closedBall (0 : ℂ) ((D.r' + D.r) / 2)) := isCompact_closedBall _ _
  have hcont : ContinuousOn (b3Rest_coef hE1.out α.form D.q) (closedBall 0 ((D.r' + D.r) / 2)) :=
    fun z hz ↦ (b3Rest_continuousAt_coef hE1.out α.isSmooth D.q (D.mem z (by
      have := mem_closedBall_zero_iff.1 hz; linarith [D.lt]))).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine MemLp.of_bound ?_ M ?_
  · exact (hcont.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by linarith [D.lt])))).aestronglyMeasurable measurableSet_ball |>.mono_measure le_rfl
  · rw [ae_restrict_iff' measurableSet_ball]
    exact Eventually.of_forall fun z hz ↦ hM z (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [D.lt])) hz)

theorem coef_add (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ) (q : C) (z : ℂ) :
    b3Rest_coef hE1.out (α + β) q z = b3Rest_coef hE1.out α q z + b3Rest_coef hE1.out β q z := by
  simp only [b3Rest_coef, b3Forms_loc_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
  push_cast
  ring

theorem coef_smul (c : ℝ) (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (q : C) (z : ℂ) :
    b3Rest_coef hE1.out (c • α) q z = (c : ℂ) * b3Rest_coef hE1.out α q z := by
  simp only [b3Rest_coef, b3Forms_loc_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  push_cast
  ring

/-- **Restriction of chart coefficients to the disc**, a linear map into `L²`. -/
def restr : b3Rest_SF E C →ₗ[ℝ] Lp ℂ 2 D.μ where
  toFun α := (D.memLp_coef α).toLp
  map_add' α β := by
    rw [← MemLp.toLp_add]
    congr 1
    funext z
    exact coef_add α.form β.form D.q z
  map_smul' c α := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1
    funext z
    simp only [b3Rest_SF.form_smul, coef_smul, Pi.smul_apply, Complex.real_smul]

theorem restr_ae (α : b3Rest_SF E C) :
    (D.restr α : ℂ → ℂ) =ᵐ[D.μ] b3Rest_coef hE1.out α.form D.q :=
  (D.memLp_coef α).coeFn_toLp

theorem norm_sq_Lp (f : Lp ℂ 2 D.μ) : ‖f‖ ^ 2 = ∫ z, ‖(f : ℂ → ℂ) z‖ ^ 2 ∂D.μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re]
  · congr 1
    funext z
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  · exact (L2.integrable_inner f f)

theorem re_inner_Lp (f g : Lp ℂ 2 D.μ) :
    (inner ℂ f g).re = ∫ z, ((f : ℂ → ℂ) z * conj ((g : ℂ → ℂ) z)).re ∂D.μ := by
  have hre := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  simp only [RCLike.re_to_complex] at hre
  rw [L2.inner_def, ← hre]
  congr 1
  funext z
  rw [RCLike.inner_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_restr_le (α : b3Rest_SF E C) : ‖D.restr α‖ ≤ ‖α‖ := by
  have h1 : ‖D.restr α‖ ^ 2 = ∫ z in ball 0 D.r', ‖b3Rest_coef hE1.out α.form D.q z‖ ^ 2 := by
    rw [D.norm_sq_Lp]
    exact integral_congr_ae ((D.restr_ae α).mono fun z hz ↦ by simp only [hz])
  have h2 : ‖α‖ ^ 2 = b3Rest_inner hE1.out α.form α.form := by
    rw [@norm_sq_eq_re_inner ℝ]
    rfl
  have h3 := b3Rest_integral_coef_sq_le hE1.out α.isSmooth D.q D.pos D.lt D.mem
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [h1, h2]
  exact h3

/-- The restriction as a continuous linear map. -/
def restrL : b3Rest_SF E C →L[ℝ] Lp ℂ 2 D.μ :=
  D.restr.mkContinuous 1 fun α ↦ by rw [one_mul]; exact D.norm_restr_le α

/-- **The coefficient of an `L²` form on the disc**, extending the restriction to the completion. -/
def restrL2 : b3Rest_L2 E C →L[ℝ] Lp ℂ 2 D.μ :=
  D.restrL.extend UniformSpace.Completion.toComplL

theorem restrL2_coe (α : b3Rest_SF E C) :
    D.restrL2 (α : b3Rest_L2 E C) = D.restr α :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) α

/-- The pairing with a form supported in the disc, for smooth forms. -/
theorem inner_eq_restr (α φ : b3Rest_SF E C)
    (hφ : tsupport φ.form ⊆ b3Rest_reg hE1.out D.q D.r') :
    inner ℝ α φ = (inner ℂ (D.restr α) (D.restr φ)).re := by
  rw [b3Rest_SF.inner_def, b3Rest_inner_eq_disc hE1.out α.isSmooth φ.isSmooth D.q
    (fun z hz ↦ D.mem' hz) hφ, D.re_inner_Lp]
  refine integral_congr_ae ?_
  filter_upwards [D.restr_ae α, D.restr_ae φ] with z h1 h2
  rw [h1, h2]

/-- **The pairing of an `L²` form with a form supported in the disc** is the `L²` pairing of
coefficients. -/
theorem inner_eq_restrL2 (h : b3Rest_L2 E C) (φ : b3Rest_SF E C)
    (hφ : tsupport φ.form ⊆ b3Rest_reg hE1.out D.q D.r') :
    inner ℝ h (φ : b3Rest_L2 E C) = (inner ℂ (D.restrL2 h) (D.restr φ)).re := by
  induction h using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_id.inner continuous_const)
      (Complex.continuous_re.comp (D.restrL2.continuous.inner continuous_const))
  | ih α =>
    rw [UniformSpace.Completion.inner_coe, D.restrL2_coe]
    exact D.inner_eq_restr α φ hφ

/-! ### Test functions of the disc -/

theorem tsupport_fun_subset (F : C → ℝ) :
    tsupport (b3Forms_fun (E := E) F) ⊆ tsupport F := by
  refine closure_mono fun p hp ↦ ?_
  intro h0
  apply hp
  show constOfIsEmpty ℝ E (Fin 0) (F p) = 0
  rw [h0]
  ext v
  simp

theorem tsupport_star_subset (β : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    tsupport (b3Forms_star β) ⊆ tsupport β := by
  refine closure_mono fun p hp ↦ ?_
  intro h0
  apply hp
  simp [b3Forms_star, h0, b3Rest_starPt_zero]

/-- The `∂̄` of a real function, as a complex function. -/
theorem dbar_ofReal {g : ℂ → ℝ} (hg : Differentiable ℝ g) (z : ℂ) :
    b3Rest_dbar (fun w ↦ (g w : ℂ)) z = (fderiv ℝ g z 1 : ℂ) + Complex.I * (fderiv ℝ g z Complex.I : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt).comp z (hg z).hasFDerivAt
  have h' : fderiv ℝ (fun w ↦ (g w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ g z) := h.fderiv
  rw [b3Rest_dbar, h']
  rfl

variable (h : b3Rest_L2 E C)

/-- The product of an `L²` coefficient with the `∂̄` of a real test function is integrable. -/
theorem integrable_mul_dbar {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Integrable (fun z ↦ (D.restrL2 h : ℂ → ℂ) z * b3Rest_dbar (fun w ↦ (g w : ℂ)) z) D.μ := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hu : Integrable (D.restrL2 h : ℂ → ℂ) D.μ := (Lp.memLp (D.restrL2 h)).integrable one_le_two
  have hdc : Continuous (b3Rest_dbar fun w ↦ (g w : ℂ)) := by
    have : (b3Rest_dbar fun w ↦ (g w : ℂ)) =
        fun z ↦ (fderiv ℝ g z 1 : ℂ) + Complex.I * (fderiv ℝ g z Complex.I : ℂ) :=
      funext (dbar_ofReal hgd)
    rw [this]
    have hc := hg.continuous_fderiv (by simp)
    fun_prop
  have hdcs : HasCompactSupport (b3Rest_dbar fun w ↦ (g w : ℂ)) := by
    refine hgc.mono' fun z hz ↦ ?_
    by_contra hz'
    apply hz
    simp [b3Rest_dbar, b3Rest_fderiv_eq_zero_of_notMem (ψ := fun w ↦ (g w : ℂ))
      (fun h' ↦ hz' (tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero g h'))]
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support hdcs
  exact hu.mul_bdd hdc.aestronglyMeasurable (Eventually.of_forall hM)

/-- **The weak Cauchy–Riemann equation for a real test function.** -/
theorem integral_dbar_real (hEx : h ∈ (b3Rest_Ex E C)ᗮ) (hCo : h ∈ (b3Rest_Co E C)ᗮ)
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ ball 0 D.r') :
    ∫ z in ball 0 D.r', (D.restrL2 h : ℂ → ℂ) z * b3Rest_dbar (fun w ↦ (g w : ℂ)) z = 0 := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hr' : ∀ z : ℂ, ‖z‖ < D.r' → b3Rest_ζ hE1.out D.q z ∈ (chartAt E D.q).target :=
    fun z hz ↦ D.mem' hz
  have hFs : b3Rest_SmoothFun (E := E) (b3Rest_cfun hE1.out D.q g) :=
    b3Rest_smoothFun_cfun hE1.out D.q hg hgc fun z hz ↦ hr' z (mem_ball_zero_iff.1 (hgs hz))
  have hFreg : tsupport (b3Rest_cfun hE1.out D.q g) ⊆ b3Rest_reg hE1.out D.q D.r' :=
    b3Rest_tsupport_cfun_reg hE1.out D.q hgc hgs hr'
  have hdreg : tsupport (b3Rest_dSF hFs).form ⊆ b3Rest_reg hE1.out D.q D.r' :=
    (b3Forms_tsupport_d_subset _).trans ((tsupport_fun_subset _).trans hFreg)
  have hsdreg : tsupport (b3Rest_sdSF hFs).form ⊆ b3Rest_reg hE1.out D.q D.r' :=
    (tsupport_star_subset _).trans hdreg
  have h1 : inner ℝ h ((b3Rest_dSF hFs : b3Rest_SF E C) : b3Rest_L2 E C) = 0 :=
    (Submodule.mem_orthogonal' _ _).1 hEx _ (Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨⟨_, hFs⟩, rfl⟩))
  have h2 : inner ℝ h ((b3Rest_sdSF hFs : b3Rest_SF E C) : b3Rest_L2 E C) = 0 :=
    (Submodule.mem_orthogonal' _ _).1 hCo _ (Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨⟨_, hFs⟩, rfl⟩))
  rw [D.inner_eq_restrL2 h _ hdreg, D.re_inner_Lp] at h1
  rw [D.inner_eq_restrL2 h _ hsdreg, D.re_inner_Lp] at h2
  set u := (D.restrL2 h : ℂ → ℂ)
  have hcd : ∀ z ∈ ball (0 : ℂ) D.r', b3Rest_coef hE1.out (b3Rest_dSF hFs).form D.q z =
      conj (b3Rest_dbar (fun w ↦ (g w : ℂ)) z) := by
    intro z hz
    rw [dbar_ofReal hgd]
    simp only [b3Rest_dSF, b3Rest_SF.form_mk]
    rw [b3Rest_coef_d_cfun hE1.out D.q hgd hFs (hr' z (mem_ball_zero_iff.1 hz))]
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hcsd : ∀ z ∈ ball (0 : ℂ) D.r', b3Rest_coef hE1.out (b3Rest_sdSF hFs).form D.q z =
      -Complex.I * conj (b3Rest_dbar (fun w ↦ (g w : ℂ)) z) := by
    intro z hz
    simp only [b3Rest_sdSF, b3Rest_SF.form_mk]
    rw [b3Rest_coef_star hE1.out _ D.q (hr' z (mem_ball_zero_iff.1 hz)), ← hcd z hz]
    rfl
  have hint := D.integrable_mul_dbar h hg hgc
  set W := ∫ z in ball 0 D.r', u z * b3Rest_dbar (fun w ↦ (g w : ℂ)) z
  have hre : W.re = 0 := by
    rw [← h1]
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [show W = ∫ z, u z * b3Rest_dbar (fun w ↦ (g w : ℂ)) z ∂D.μ from rfl, ← this]
    refine integral_congr_ae ?_
    filter_upwards [D.restr_ae (b3Rest_dSF hFs), ae_restrict_mem measurableSet_ball] with z hz hzb
    rw [hz, hcd z hzb, Complex.conj_conj]
  have him : W.im = 0 := by
    have := integral_im hint
    simp only [RCLike.im_to_complex] at this
    rw [show W = ∫ z, u z * b3Rest_dbar (fun w ↦ (g w : ℂ)) z ∂D.μ from rfl, ← this]
    have h2' : ∫ z, -(u z * b3Rest_dbar (fun w ↦ (g w : ℂ)) z).im ∂D.μ = 0 := by
      rw [← h2]
      refine integral_congr_ae ?_
      filter_upwards [D.restr_ae (b3Rest_sdSF hFs), ae_restrict_mem measurableSet_ball]
        with z hz hzb
      rw [hz, hcsd z hzb]
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj, Complex.mul_re,
        Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
      ring
    rw [integral_neg, neg_eq_zero] at h2'
    exact h2'
  exact Complex.ext hre him

/-- **The weak Cauchy–Riemann equation** for the coefficient of a weakly harmonic form. -/
theorem integral_dbar (hEx : h ∈ (b3Rest_Ex E C)ᗮ) (hCo : h ∈ (b3Rest_Co E C)ᗮ)
    {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ ball 0 D.r') :
    ∫ z, (D.restrL2 h : ℂ → ℂ) z * b3Rest_dbar ψ z = 0 := by
  set u := (D.restrL2 h : ℂ → ℂ)
  set ψ₁ : ℂ → ℝ := fun z ↦ (ψ z).re
  set ψ₂ : ℂ → ℝ := fun z ↦ (ψ z).im
  have h1s : ContDiff ℝ ∞ ψ₁ := Complex.reCLM.contDiff.comp hψ
  have h2s : ContDiff ℝ ∞ ψ₂ := Complex.imCLM.contDiff.comp hψ
  have hts1 : tsupport ψ₁ ⊆ tsupport ψ := tsupport_comp_subset (g := Complex.re) rfl ψ
  have hts2 : tsupport ψ₂ ⊆ tsupport ψ := tsupport_comp_subset (g := Complex.im) rfl ψ
  have hc1 : HasCompactSupport ψ₁ := hψc.mono' ((subset_tsupport _).trans hts1)
  have hc2 : HasCompactSupport ψ₂ := hψc.mono' ((subset_tsupport _).trans hts2)
  have hW1 := D.integral_dbar_real h hEx hCo h1s hc1 (hts1.trans hψs)
  have hW2 := D.integral_dbar_real h hEx hCo h2s hc2 (hts2.trans hψs)
  have hdbar : ∀ z, b3Rest_dbar ψ z = b3Rest_dbar (fun w ↦ (ψ₁ w : ℂ)) z +
      Complex.I * b3Rest_dbar (fun w ↦ (ψ₂ w : ℂ)) z := by
    intro z
    have hψe : ψ = (fun w ↦ (ψ₁ w : ℂ)) + Complex.I • (fun w ↦ (ψ₂ w : ℂ)) := by
      funext w
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ψ₁, ψ₂]
      rw [mul_comm]
      exact (Complex.re_add_im _).symm
    have hd1 : DifferentiableAt ℝ (fun w ↦ (ψ₁ w : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z ((h1s.differentiable (by simp)) z)
    have hd2 : DifferentiableAt ℝ (fun w ↦ (ψ₂ w : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z ((h2s.differentiable (by simp)) z)
    have hf : fderiv ℝ ψ z = fderiv ℝ (fun w ↦ (ψ₁ w : ℂ)) z +
        Complex.I • fderiv ℝ (fun w ↦ (ψ₂ w : ℂ)) z := by
      conv_lhs => rw [hψe]
      rw [fderiv_add hd1 (hd2.const_smul Complex.I), fderiv_const_smul hd2]
    simp only [b3Rest_dbar, hf, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hzero : ∀ z ∉ ball (0 : ℂ) D.r', u z * b3Rest_dbar ψ z = 0 := by
    intro z hz
    have : z ∉ tsupport ψ := fun h' ↦ hz (hψs h')
    simp [b3Rest_dbar, b3Rest_fderiv_eq_zero_of_notMem this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp only [hdbar, mul_add]
  have i1 := D.integrable_mul_dbar h h1s hc1
  have i2 := D.integrable_mul_dbar h h2s hc2
  rw [integral_add i1 (by simpa only [mul_left_comm] using i2.const_mul Complex.I)]
  simp only [mul_left_comm (u _) Complex.I]
  rw [integral_const_mul, hW1, hW2, mul_zero, add_zero]

/-- **Weyl's lemma for a weakly harmonic form**: on the half disc its coefficient is almost
everywhere a holomorphic function. -/
theorem exists_holomorphic (hEx : h ∈ (b3Rest_Ex E C)ᗮ) (hCo : h ∈ (b3Rest_Co E C)ᗮ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 (D.r' / 2)) ∧
      ∀ᵐ z, z ∈ ball (0 : ℂ) (D.r' / 2) → (D.restrL2 h : ℂ → ℂ) z = G z := by
  have hu : IntegrableOn (D.restrL2 h : ℂ → ℂ) (ball 0 D.r') :=
    (Lp.memLp (D.restrL2 h)).integrable one_le_two
  exact b3Rest_weyl D.pos hu fun ψ h1 h2 h3 ↦ D.integral_dbar h hEx hCo h1 h2 h3

/-- The coefficient of a form vanishes off its support. -/
theorem coef_eq_zero_of_notMem {φ : C → E [⋀^Fin 1]→L[ℝ] ℝ} {z : ℂ}
    (hz : (chartAt E D.q).symm (b3Rest_ζ hE1.out D.q z) ∉ tsupport φ) :
    b3Rest_coef hE1.out φ D.q z = 0 := by
  have h0 : φ ((chartAt E D.q).symm (b3Rest_ζ hE1.out D.q z)) = 0 :=
    image_eq_zero_of_notMem_tsupport hz
  simp [b3Rest_coef, b3Forms_loc, h0]

/-- **The pairing of a weakly harmonic form with a form supported in the half disc**, through its
holomorphic coefficient. -/
theorem inner_eq_holomorphic {G : ℂ → ℂ}
    (hG : ∀ᵐ z, z ∈ ball (0 : ℂ) (D.r' / 2) → (D.restrL2 h : ℂ → ℂ) z = G z)
    (φ : b3Rest_SF E C) (hφ : tsupport φ.form ⊆ b3Rest_reg hE1.out D.q (D.r' / 2)) :
    inner ℝ h (φ : b3Rest_L2 E C) =
      ∫ z in ball 0 (D.r' / 2), (G z * conj (b3Rest_coef hE1.out φ.form D.q z)).re := by
  have hsub : ball (0 : ℂ) (D.r' / 2) ⊆ ball 0 D.r' := ball_subset_ball (by linarith [D.pos])
  have hreg : b3Rest_reg hE1.out D.q (D.r' / 2) ⊆ b3Rest_reg hE1.out D.q D.r' := by
    rintro p ⟨hp, w, hw, hw'⟩
    exact ⟨hp, w, hsub hw, hw'⟩
  rw [D.inner_eq_restrL2 h φ (hφ.trans hreg), D.re_inner_Lp]
  have hae : (fun z ↦ ((D.restrL2 h : ℂ → ℂ) z * conj ((D.restr φ : ℂ → ℂ) z)).re) =ᵐ[D.μ]
      fun z ↦ ((D.restrL2 h : ℂ → ℂ) z * conj (b3Rest_coef hE1.out φ.form D.q z)).re := by
    filter_upwards [D.restr_ae φ] with z hz
    rw [hz]
  rw [integral_congr_ae hae]
  have hzero : ∀ z ∈ ball (0 : ℂ) D.r' \ ball 0 (D.r' / 2),
      ((D.restrL2 h : ℂ → ℂ) z * conj (b3Rest_coef hE1.out φ.form D.q z)).re = 0 := by
    rintro z ⟨hz, hz'⟩
    rw [D.coef_eq_zero_of_notMem (fun hmem ↦ ?_), _root_.map_zero, mul_zero, Complex.zero_re]
    obtain ⟨-, w, hw, hw'⟩ := hφ hmem
    rw [(chartAt E D.q).right_inv (D.mem' (mem_ball_zero_iff.1 hz))] at hw'
    exact hz' (b3Rest_ζ_injective hE1.out D.q hw' ▸ hw)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub hzero]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [hG] with z hz hzb
  rw [hz hzb]

end b3Rest_Disc

end HodgeLean.Foundations.Program
