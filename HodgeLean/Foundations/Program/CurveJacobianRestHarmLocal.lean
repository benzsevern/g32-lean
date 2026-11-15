import HodgeLean.Foundations.Program.CurveJacobianRestExtract
import HodgeLean.Foundations.Program.CurveJacobianAExact

/-! # Track B3, lane Rest: local harmonic representatives

For a weakly harmonic `L²` form `h` and a point `p₀`, Weyl's lemma gives a holomorphic `G` on a
disc of the chart at `p₀` computing the pairings of `h` with forms supported there
(`b3Rest_Disc.inner_eq_holomorphic`). Cutting `Re (G dz)` off near the boundary of the disc gives
a smooth form `β` (`b3Rest_exists_local_harmonic`) with
* `⟨h, φ⟩ = ⟨β, φ⟩` for every smooth form `φ` supported near `p₀`;
* `dβ = 0` and `d⋆β = 0` near `p₀`: there `β = d (Re F)` and `⋆β = d (Re (-i F))` for a
  holomorphic primitive `F` of `G`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff ComplexConjugate

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The covector `v ↦ Re (w κ(v))` of the model line (`κ(v) e = v`), as a `1`-form. -/
def b3Rest_ellLin (hE : Module.finrank ℂ E = 1) : ℂ →ₗ[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) where
  toFun w := ofSubsingleton ℝ E ℝ (0 : Fin 1)
    (Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ w).comp
      ((b3Rest_L hE).symm : E →L[ℝ] ℂ)))
  map_add' w w' := by
    ext v
    simp
  map_smul' c w := by
    ext v
    simp [mul_assoc]

/-- The covector `v ↦ Re (w κ(v))`, a continuous linear function of `w`. -/
def b3Rest_ell (hE : Module.finrank ℂ E = 1) : ℂ →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap (b3Rest_ellLin hE)

theorem b3Rest_ell_apply (hE : Module.finrank ℂ E = 1) (w : ℂ) (v : E) :
    b3Rest_ell hE w (fun _ ↦ v) = (w * (b3Rest_L hE).symm v).re := by
  simp [b3Rest_ell, b3Rest_ellLin]

theorem b3Rest_L_symm_e (hE : Module.finrank ℂ E = 1) : (b3Rest_L hE).symm (b3Rest_e hE) = 1 := by
  rw [ContinuousLinearEquiv.symm_apply_eq, b3Rest_L_apply, one_smul]

theorem b3Rest_L_symm_Ie (hE : Module.finrank ℂ E = 1) :
    (b3Rest_L hE).symm (Complex.I • b3Rest_e hE) = Complex.I := by
  rw [ContinuousLinearEquiv.symm_apply_eq, b3Rest_L_apply]

/-- The chart coefficient of `v ↦ Re (w κ(v))` is `w`. -/
theorem b3Rest_ell_coef (hE : Module.finrank ℂ E = 1) (w : ℂ) :
    ((b3Rest_ell hE w (fun _ ↦ b3Rest_e hE) : ℝ) : ℂ) -
      Complex.I * (b3Rest_ell hE w (fun _ ↦ Complex.I • b3Rest_e hE) : ℂ) = w := by
  rw [b3Rest_ell_apply, b3Rest_ell_apply, b3Rest_L_symm_e, b3Rest_L_symm_Ie, mul_one]
  apply Complex.ext <;> simp

theorem b3Rest_L_symm_smul (hE : Module.finrank ℂ E = 1) (c : ℂ) (v : E) :
    (b3Rest_L hE).symm (c • v) = c * (b3Rest_L hE).symm v := by
  have : ∀ v, (b3Rest_L hE).symm v = (b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).symm v :=
    fun _ ↦ rfl
  rw [this, this, map_smul, smul_eq_mul]

theorem b3Rest_starPt_ell (hE : Module.finrank ℂ E = 1) (w : ℂ) :
    b3Forms_starPt (b3Rest_ell hE w) = b3Rest_ell hE (-Complex.I * w) := by
  ext v
  have hv : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [hv, b3Forms_starPt_apply, b3Rest_ell_apply, b3Rest_ell_apply, b3Rest_L_symm_smul]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im]
  ring

/-! ## Closedness from a holomorphic primitive -/

/-- **`Re (H dz)` is closed** where `H` has a holomorphic primitive: there it is `d (Re Φ)`. -/
theorem b3Rest_extDeriv_ell_eq_zero (hE : Module.finrank ℂ E = 1) {H Φ : ℂ → ℂ} (c : E)
    {ρ : ℝ} (hΦ : ∀ z ∈ ball (0 : ℂ) ρ, HasDerivAt Φ (H z) z) {u : E}
    (hu : (b3Rest_L hE).symm (u - c) ∈ ball (0 : ℂ) ρ) :
    extDeriv (fun u' ↦ b3Rest_ell hE (H ((b3Rest_L hE).symm (u' - c)))) u = 0 := by
  set ψ : E → ℂ := fun u' ↦ (b3Rest_L hE).symm (u' - c)
  have hψc : Continuous ψ := (b3Rest_L hE).symm.continuous.comp (continuous_id.sub continuous_const)
  have hU : ψ ⁻¹' ball (0 : ℂ) ρ ∈ 𝓝 u := hψc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hu)
  have hψd : ∀ u', HasFDerivAt ψ ((b3Rest_L hE).symm : E →L[ℝ] ℂ) u' := by
    intro u'
    have h := ((b3Rest_L hE).symm : E →L[ℝ] ℂ).hasFDerivAt.comp u'
      ((hasFDerivAt_id u').sub_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  set Ω : E → E [⋀^Fin 0]→L[ℝ] ℝ := fun u' ↦ constOfIsEmpty ℝ E (Fin 0) ((Φ (ψ u')).re)
  have hΦd : DifferentiableOn ℂ Φ (ball 0 ρ) := fun z hz ↦ (hΦ z hz).differentiableAt.differentiableWithinAt
  have hΦs : ContDiffOn ℝ ∞ Φ (ball 0 ρ) :=
    ((hΦd.contDiffOn isOpen_ball).restrict_scalars ℝ)
  have hfd : ∀ u' ∈ ψ ⁻¹' ball (0 : ℂ) ρ,
      HasFDerivAt (fun x ↦ (Φ (ψ x)).re)
        (Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ (H (ψ u'))).comp
          ((b3Rest_L hE).symm : E →L[ℝ] ℂ))) u' := by
    intro u' hu'
    have h1 : HasFDerivAt Φ ((ContinuousLinearMap.mul ℝ ℂ (H (ψ u')))) (ψ u') := by
      have := (hΦ (ψ u') hu').hasFDerivAt.restrictScalars ℝ
      convert this using 1
      ext; simp [mul_comm]
    exact Complex.reCLM.hasFDerivAt.comp u' (h1.comp u' (hψd u'))
  have hev : (fun u' ↦ b3Rest_ell hE (H (ψ u'))) =ᶠ[𝓝 u] fun u' ↦ extDeriv Ω u' := by
    filter_upwards [hU] with u' hu'
    rw [show Ω = fun x ↦ constOfIsEmpty ℝ E (Fin 0) ((Φ (ψ x)).re) from rfl,
      extDeriv_constOfIsEmpty, (hfd u' hu').fderiv]
    rfl
  rw [hev.extDeriv_eq]
  refine extDeriv_extDeriv_apply (r := ∞) ?_ b3Forms_minSmoothness_le
  have hcomp : ContDiffAt ℝ ∞ (fun x ↦ (Φ (ψ x)).re) u :=
    Complex.reCLM.contDiff.contDiffAt.comp u
      ((hΦs.contDiffAt (isOpen_ball.mem_nhds hu)).comp u
        ((((b3Rest_L hE).symm : E →L[ℝ] ℂ).contDiff.comp
          (contDiff_id.sub contDiff_const)).contDiffAt))
  exact (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).toContinuousLinearEquiv.contDiff.contDiffAt.comp u hcomp

attribute [local instance] b3Forms_isManifold_real

/-- A form whose local representative vanishes at a point vanishes there. -/
theorem b3Rest_eq_zero_of_loc_eq_zero {k : ℕ} {γ : C → E [⋀^Fin k]→L[ℝ] ℝ} {x z : C}
    (hz : z ∈ (chartAt E x).source) (h : b3Forms_loc γ x (chartAt E x z) = 0) : γ z = 0 := by
  rw [b3Forms_loc_chart γ hz] at h
  have hu : chartAt E z z ∈ b3Forms_trDom z x :=
    ⟨(chartAt E z).map_source (mem_chart_source E z), by
      show (chartAt E z).symm (chartAt E z z) ∈ (chartAt E x).source
      rw [(chartAt E z).left_inv (mem_chart_source E z)]; exact hz⟩
  have hchain := b3Forms_fderiv_tr_comp (x := z) (y := x) (z := z) hu (by
    rw [(chartAt E z).left_inv (mem_chart_source E z)]; exact mem_chart_source E z)
  rw [b3Forms_fderiv_tr_self ((chartAt E z).map_source (mem_chart_source E z))] at hchain
  have htr : b3Forms_tr z x (chartAt E z z) = chartAt E x z := by
    simp [b3Forms_tr, (chartAt E z).left_inv (mem_chart_source E z)]
  rw [htr] at hchain
  have : γ z = ((γ z).compContinuousLinearMap (fderiv ℝ (b3Forms_tr x z) (chartAt E x z))).compContinuousLinearMap
      (fderiv ℝ (b3Forms_tr z x) (chartAt E z z)) := by
    ext v
    simp only [compContinuousLinearMap_apply]
    congr 1
    funext i
    have := congrArg (fun L : E →L[ℝ] E ↦ L (v i)) hchain
    simpa using this
  rw [this, h]
  ext v
  simp

/-! ## The local harmonic representative -/

section Local

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_contDiff_cut_mul {g : ℂ → ℝ} {G : ℂ → ℂ} {ρ : ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 ρ) (hG : DifferentiableOn ℂ G (ball 0 ρ)) :
    ContDiff ℝ ∞ (fun z ↦ (g z : ℂ) * G z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ ball (0 : ℂ) ρ
  · have hGs : ContDiffAt ℝ ∞ G z :=
      (((hG.contDiffOn isOpen_ball).restrict_scalars ℝ).contDiffAt (isOpen_ball.mem_nhds hz))
    exact (Complex.ofRealCLM.contDiff.comp hg).contDiffAt.mul hGs
  · have hz' : z ∉ tsupport g := fun h ↦ hz (hgs h)
    refine contDiffAt_const (c := (0 : ℂ)) |>.congr_of_eventuallyEq ?_
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hz')] with w hw
    rw [hw]
    simp

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]
  [hE1 : Fact (Module.finrank ℂ E = 1)]

/-- **A local harmonic representative of a weakly harmonic form**: near each point a smooth form
`β`, closed and coclosed there, has the pairings of `h` with forms supported there. -/
theorem b3Rest_exists_local_harmonic (h : b3Rest_L2 E C) (hEx : h ∈ (b3Rest_Ex E C)ᗮ)
    (hCo : h ∈ (b3Rest_Co E C)ᗮ) (p₀ : C) :
    ∃ β : b3Rest_SF E C, ∃ U : Set C, IsOpen U ∧ p₀ ∈ U ∧
      (∀ φ : b3Rest_SF E C, tsupport φ.form ⊆ U →
        inner ℝ h (φ : b3Rest_L2 E C) = inner ℝ (β : b3Rest_L2 E C) (φ : b3Rest_L2 E C)) ∧
      ∀ p ∈ U, b3Forms_d β.form p = 0 ∧ b3Forms_d (b3Forms_star β.form) p = 0 := by
  have hE := hE1.out
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius (b3Rest_e hE) (b3Rest_e_ne_zero hE) p₀
  let D : b3Rest_Disc (E := E) C := ⟨p₀, R, R / 2, by positivity, by linarith, hR⟩
  obtain ⟨G, hGd, hGae⟩ := D.exists_holomorphic h hEx hCo
  set ρ := R / 4 with hρ
  have hρ' : D.r' / 2 = ρ := by simp only [D, hρ]; ring
  rw [hρ'] at hGd hGae
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨g, hg, hgc, hgs, hg01, hg1⟩ := b3Rest_exists_bump (r₁ := ρ / 2) (r₂ := 3 * ρ / 4)
    (by positivity) (by linarith)
  have hgs' : tsupport g ⊆ ball 0 ρ := hgs.trans (ball_subset_ball (by linarith))
  set W : ℂ → ℂ := fun z ↦ (g z : ℂ) * G z
  have hW : ContDiff ℝ ∞ W := b3Rest_contDiff_cut_mul hg hgs' hGd
  set c := chartAt E p₀ p₀
  set ψ : E → ℂ := fun u ↦ (b3Rest_L hE).symm (u - c)
  have hψ : ContDiff ℝ ∞ ψ := (b3Rest_L hE).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  set A : E → E [⋀^Fin 1]→L[ℝ] ℝ := fun u ↦ b3Rest_ell hE (W (ψ u))
  have hA : ContDiff ℝ ∞ A := (b3Rest_ell hE).contDiff.comp (hW.comp hψ)
  have hR' : ∀ z : ℂ, ‖z‖ < R → b3Rest_ζ hE p₀ z ∈ (chartAt E p₀).target := hR
  have hψζ : ∀ z, ψ (b3Rest_ζ hE p₀ z) = z := b3Rest_L_symm_ζ hE p₀
  have hζψ : ∀ u, b3Rest_ζ hE p₀ (ψ u) = u := fun u ↦ by
    show c + ψ u • b3Rest_e hE = u
    rw [← b3Rest_L_apply, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  have hζc : Continuous (b3Rest_ζ hE p₀) := by
    show Continuous fun z : ℂ ↦ c + z • b3Rest_e hE
    fun_prop
  -- support of `A`
  have hAsupp : tsupport A ⊆ b3Rest_ζ hE p₀ '' tsupport g := by
    refine closure_minimal (fun u hu ↦ ?_) (hgc.isCompact.image hζc).isClosed
    have hgu : g (ψ u) ≠ 0 := by
      intro h0
      apply hu
      simp [A, W, h0]
    exact ⟨ψ u, subset_closure hgu, hζψ u⟩
  have hAc : HasCompactSupport A :=
    (hgc.isCompact.image hζc).of_isClosed_subset (isClosed_tsupport _) hAsupp
  have hAt : tsupport A ⊆ (chartAt E p₀).target := by
    refine hAsupp.trans ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hR z (by have := mem_ball_zero_iff.1 (hgs' hz); linarith)
  let β : b3Rest_SF E C := b3Rest_SF.mk (b3Rest_ofLoc p₀ A) (b3Rest_isSmooth_ofLoc p₀ hA hAc hAt)
  have hlocβ : ∀ u ∈ (chartAt E p₀).target, b3Forms_loc β.form p₀ u = A u := fun u hu ↦
    b3Rest_loc_ofLoc_self p₀ A hu
  have hcoefβ : ∀ z : ℂ, ‖z‖ < R → b3Rest_coef hE β.form p₀ z = W z := by
    intro z hz
    rw [b3Rest_coef, hlocβ (b3Rest_ζ hE p₀ z) (hR z hz)]
    simp only [A, hψζ]
    exact b3Rest_ell_coef hE (W z)
  -- the open set `U`
  have hregeq : ∀ r, b3Rest_reg hE p₀ r = (chartAt E p₀).source ∩ chartAt E p₀ ⁻¹' (ψ ⁻¹' ball 0 r) := by
    intro r
    ext p
    simp only [b3Rest_reg, mem_inter_iff, mem_preimage, mem_image]
    constructor
    · rintro ⟨hp, z, hz, hzp⟩
      exact ⟨hp, by rw [← hzp, hψζ]; exact hz⟩
    · rintro ⟨hp, hpz⟩
      exact ⟨hp, ψ (chartAt E p₀ p), hpz, hζψ _⟩
  refine ⟨β, b3Rest_reg hE p₀ (ρ / 2), ?_, ?_, ?_, ?_⟩
  · rw [hregeq]
    exact (chartAt E p₀).continuousOn.isOpen_inter_preimage (chartAt E p₀).open_source
      (isOpen_ball.preimage hψ.continuous)
  · rw [hregeq]
    refine ⟨mem_chart_source E p₀, ?_⟩
    simp [ψ, c, hρ0]
  · intro φ hφ
    have hsub : b3Rest_reg hE p₀ (ρ / 2) ⊆ b3Rest_reg hE p₀ ρ := by
      rintro p ⟨hp, w, hw, hw'⟩
      exact ⟨hp, w, ball_subset_ball (by linarith) hw, hw'⟩
    have h1 := D.inner_eq_holomorphic h (hρ' ▸ hGae) φ (hρ' ▸ (hφ.trans hsub))
    rw [hρ'] at h1
    rw [h1, UniformSpace.Completion.inner_coe, b3Rest_SF.inner_def,
      b3Rest_inner_eq_disc hE β.isSmooth φ.isSmooth p₀
        (fun z hz ↦ hR z (by linarith)) (hφ.trans hsub)]
    refine setIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
    rw [hcoefβ z (by have := mem_ball_zero_iff.1 hz; linarith)]
    by_cases hz2 : z ∈ ball (0 : ℂ) (ρ / 2)
    · simp only [W, hg1 z (ball_subset_closedBall hz2), Complex.ofReal_one, one_mul]
      rfl
    · rw [D.coef_eq_zero_of_notMem (z := z) (φ := φ.form) (fun hmem ↦ ?_)]
      · simp
      obtain ⟨-, w, hw, hw'⟩ := hφ hmem
      have hw2 : b3Rest_ζ hE p₀ w = chartAt E p₀ ((chartAt E p₀).symm (b3Rest_ζ hE p₀ z)) := hw'
      rw [(chartAt E p₀).right_inv (hR' z (by have := mem_ball_zero_iff.1 hz; linarith))] at hw2
      exact hz2 (b3Rest_ζ_injective hE p₀ hw2 ▸ hw)
  · intro p hp
    obtain ⟨F, hF⟩ := hGd.isExactOn_ball
    rw [hregeq] at hp
    obtain ⟨hps, hpu⟩ := hp
    set u := chartAt E p₀ p
    have hu : u ∈ (chartAt E p₀).target := (chartAt E p₀).map_source hps
    have hψu : ψ u ∈ ball (0 : ℂ) (ρ / 2) := hpu
    have hψu' : ψ u ∈ ball (0 : ℂ) ρ := ball_subset_ball (by linarith) hψu
    have hnb : ψ ⁻¹' ball (0 : ℂ) (ρ / 2) ∈ 𝓝 u :=
      hψ.continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hψu)
    have hA_ev : A =ᶠ[𝓝 u] fun u' ↦ b3Rest_ell hE (G (ψ u')) := by
      filter_upwards [hnb] with u' hu'
      simp only [A, W, hg1 (ψ u') (ball_subset_closedBall hu'), Complex.ofReal_one, one_mul]
    have hlocev : b3Forms_loc β.form p₀ =ᶠ[𝓝 u] A := by
      filter_upwards [(chartAt E p₀).open_target.mem_nhds hu] with u' hu'
      exact hlocβ u' hu'
    constructor
    · apply b3Rest_eq_zero_of_loc_eq_zero hps
      rw [b3Forms_loc_d β.isSmooth p₀ hu, (hlocev.trans hA_ev).extDeriv_eq]
      exact b3Rest_extDeriv_ell_eq_zero hE c hF hψu'
    · apply b3Rest_eq_zero_of_loc_eq_zero hps
      rw [b3Forms_loc_d β.isSmooth.star p₀ hu]
      have hev2 : b3Forms_loc (b3Forms_star β.form) p₀ =ᶠ[𝓝 u]
          fun u' ↦ b3Rest_ell hE (-Complex.I * G (ψ u')) := by
        filter_upwards [(chartAt E p₀).open_target.mem_nhds hu, hnb] with u' hu' hu''
        rw [b3Forms_loc_star _ hu', hlocβ u' hu']
        simp only [A, W, hg1 (ψ u') (ball_subset_closedBall hu''), Complex.ofReal_one, one_mul]
        exact b3Rest_starPt_ell hE _
      rw [hev2.extDeriv_eq]
      exact b3Rest_extDeriv_ell_eq_zero hE c (Φ := fun z ↦ -Complex.I * F z)
        (fun z hz ↦ (hF z hz).const_mul (-Complex.I)) hψu'

end Local

end HodgeLean.Foundations.Program
