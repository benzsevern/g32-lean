import HodgeLean.Foundations.Program.CurveJacobianRestGlue
import HodgeLean.Foundations.Program.CurveJacobianRestParam
import HodgeLean.Foundations.Program.CurveJacobianRestTransverse

/-! # Track B3, lane Rest: smeared segments

In the chart at `x`, with complex coordinate `z ↦ φ_x(x) + z e`, the **smeared segment** from `a`
to `b` is the vector field `X(z) = (∫₀¹ ρ_ε(z - a - τ (b - a)) dτ) (b - a)`, and the `1`-form
`ι X` (`ι X (v) = Im (conj X · v)`) satisfies `(A ∧ ι X)(e, i e) = A(X)`. For a closed form `ω`
with primitive `h` on a convex chart region containing the `ε`-neighbourhood of the segment,
`∫_C ω ∧ ι X = ∫ ρ_ε(w) (h(b + w) - h(a + w)) dw` (`b3Rest_integral_wedge_smear`): Fubini, a
translation, and the fundamental theorem of calculus along the translated segments.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff ComplexConjugate

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The covector `v ↦ Im (conj w · κ(v))` of the model line, `κ(v) e = v`. -/
def b3Rest_iotaLin (hE : Module.finrank ℂ E = 1) : ℂ →ₗ[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) where
  toFun w := ofSubsingleton ℝ E ℝ (0 : Fin 1)
    (Complex.imCLM.comp ((ContinuousLinearMap.mul ℝ ℂ (conj w)).comp
      ((b3Rest_L hE).symm : E →L[ℝ] ℂ)))
  map_add' w w' := by
    ext v
    simp
  map_smul' c w := by
    ext v
    simp [mul_assoc]

/-- The covector `ι w : v ↦ Im (conj w · κ(v))`, continuous linear in `w`. -/
def b3Rest_iota (hE : Module.finrank ℂ E = 1) : ℂ →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap (b3Rest_iotaLin hE)

theorem b3Rest_iota_apply (hE : Module.finrank ℂ E = 1) (w : ℂ) (v : E) :
    b3Rest_iota hE w (fun _ ↦ v) = (conj w * (b3Rest_L hE).symm v).im := by
  simp [b3Rest_iota, b3Rest_iotaLin]

/-- **`(A ∧ ι w)(e, i e) = A(w e)`.** -/
theorem b3Rest_wedge_iota (hE : Module.finrank ℂ E = 1) (A : E [⋀^Fin 1]→L[ℝ] ℝ) (w : ℂ) :
    b3Forms_wedge A (b3Rest_iota hE w) (b3Rest_b hE) = A (fun _ ↦ b3Rest_L hE w) := by
  rw [b3Forms_wedge_apply]
  simp only [b3Rest_b, b3Forms_cplxBasis_zero, b3Forms_cplxBasis_one, b3Rest_iota_apply,
    b3Rest_L_symm_e, b3Rest_L_symm_Ie]
  have hw : b3Rest_L hE w = w.re • b3Rest_e hE + w.im • (Complex.I • b3Rest_e hE) := by
    rw [b3Rest_L_apply]
    conv_lhs => rw [← Complex.re_add_im w]
    rw [add_smul, Complex.coe_smul, mul_smul, Complex.coe_smul]
  have hlin : A (fun _ ↦ b3Rest_L hE w) =
      w.re * A (fun _ ↦ b3Rest_e hE) + w.im * A (fun _ ↦ Complex.I • b3Rest_e hE) := by
    have := (b3Forms_toCLM A).map_add (w.re • b3Rest_e hE) (w.im • (Complex.I • b3Rest_e hE))
    simp only [b3Forms_toCLM_apply, map_smul, smul_eq_mul] at this
    rw [hw, this]
  rw [hlin]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, mul_one, mul_zero, Complex.I_re,
    Complex.I_im]
  ring

/-! ## The smeared segment in complex coordinates -/

section Profile

/-- The real radial bump `z ↦ e(1 - |z/ε|²)`. -/
def b3Rest_rho (ε : ℝ) (z : ℂ) : ℝ := b3Rest_bump (ε⁻¹ • z)

theorem b3Rest_rho_contDiff (ε : ℝ) : ContDiff ℝ ∞ (b3Rest_rho ε) :=
  b3Rest_bump_contDiff.comp (contDiff_const_smul _)

theorem b3Rest_rho_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ε ≤ ‖z‖) : b3Rest_rho ε z = 0 := by
  have := b3Rest_mol_eq_zero hε hz
  simpa [b3Rest_mol, b3Rest_rho] using this

theorem b3Rest_rho_nonneg (ε : ℝ) (z : ℂ) : 0 ≤ b3Rest_rho ε z := b3Rest_bump_nonneg _

/-- **The profile of the smeared segment** from `a` to `b`. -/
def b3Rest_segK (ε : ℝ) (a b : ℂ) (z : ℂ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, b3Rest_rho ε (z - a - τ • (b - a))

theorem b3Rest_segK_contDiff (ε : ℝ) (a b : ℂ) : ContDiff ℝ ∞ (b3Rest_segK ε a b) := by
  refine b3Rest_contDiff_intervalIntegral (F := fun z τ ↦ b3Rest_rho ε (z - a - τ • (b - a)))
    ?_ 0 1
  exact (b3Rest_rho_contDiff ε).comp
    ((contDiff_fst.sub contDiff_const).sub (contDiff_snd.smul contDiff_const))

theorem b3Rest_segK_eq_zero {ε : ℝ} (hε : 0 < ε) (a b : ℂ) {z : ℂ}
    (hz : z ∉ Metric.thickening ε (segment ℝ a b)) : b3Rest_segK ε a b z = 0 := by
  unfold b3Rest_segK
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ ↦ b3Rest_rho_eq_zero hε ?_
  by_contra hlt
  apply hz
  rw [Metric.mem_thickening_iff]
  refine ⟨a + τ • (b - a), ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨τ, ⟨hτ.1.le, hτ.2⟩, rfl⟩
  · rw [dist_eq_norm, show z - (a + τ • (b - a)) = z - a - τ • (b - a) by abel]
    exact not_le.1 hlt

theorem b3Rest_tsupport_segK {ε : ℝ} (hε : 0 < ε) (a b : ℂ) :
    tsupport (b3Rest_segK ε a b) ⊆ Metric.cthickening ε (segment ℝ a b) := by
  refine closure_minimal (fun z hz ↦ ?_) Metric.isClosed_cthickening
  by_contra h
  exact hz (b3Rest_segK_eq_zero hε a b fun h' ↦ h (Metric.thickening_subset_cthickening _ _ h'))

theorem b3Rest_hasCompactSupport_segK {ε : ℝ} (hε : 0 < ε) (a b : ℂ) :
    HasCompactSupport (b3Rest_segK ε a b) := by
  have hseg : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  exact (hseg.cthickening (r := ε)).of_isClosed_subset (isClosed_tsupport _)
    (b3Rest_tsupport_segK hε a b)

/-- **The derivative of the profile along the segment**: `ρ_ε(z - a) - ρ_ε(z - b)`. -/
theorem b3Rest_fderiv_segK (ε : ℝ) (a b z : ℂ) :
    fderiv ℝ (b3Rest_segK ε a b) z (b - a) = b3Rest_rho ε (z - a) - b3Rest_rho ε (z - b) := by
  set f : ℝ → ℝ := fun σ ↦ b3Rest_rho ε (z - a - σ • (b - a))
  have hfc : Continuous f :=
    (b3Rest_rho_contDiff ε).continuous.comp (continuous_const.sub (continuous_id.smul continuous_const))
  have hΦ : ∀ s : ℝ, b3Rest_segK ε a b (z + s • (b - a)) =
      (∫ σ in (0 : ℝ)..(1 - s), f σ) - ∫ σ in (0 : ℝ)..(-s), f σ := by
    intro s
    have : b3Rest_segK ε a b (z + s • (b - a)) = ∫ τ in (0 : ℝ)..1, f (τ - s) := by
      unfold b3Rest_segK
      congr 1
      funext τ
      simp only [f, sub_smul]
      congr 1
      abel
    rw [this, intervalIntegral.integral_comp_sub_right, zero_sub,
      intervalIntegral.integral_interval_sub_left (hfc.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _)]
  have h1 : HasDerivAt (fun s : ℝ ↦ ∫ σ in (0 : ℝ)..(1 - s), f σ) (f (1 - 0) * (-1)) 0 := by
    have := (intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 (1 - 0))
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_sub 1)
    exact this
  have h2 : HasDerivAt (fun s : ℝ ↦ ∫ σ in (0 : ℝ)..(-s), f σ) (f (-0) * (-1)) 0 := by
    have := (intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 (-0))
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    exact this
  have hg : HasDerivAt (fun s : ℝ ↦ b3Rest_segK ε a b (z + s • (b - a))) (f 0 - f 1) 0 := by
    have := h1.sub h2
    simp only [mul_neg, mul_one, sub_neg_eq_add, sub_zero, neg_zero] at this
    rw [show f 0 - f 1 = -f 1 + f 0 by ring]
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ hΦ s)
  have hd : HasDerivAt (fun s : ℝ ↦ b3Rest_segK ε a b (z + s • (b - a)))
      (fderiv ℝ (b3Rest_segK ε a b) z (b - a)) 0 := by
    have hk : HasFDerivAt (b3Rest_segK ε a b) (fderiv ℝ (b3Rest_segK ε a b) z)
        (z + (0 : ℝ) • (b - a)) := by
      rw [zero_smul, add_zero]
      exact ((b3Rest_segK_contDiff ε a b).differentiable (by simp) z).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ ↦ z + s • (b - a)) (b - a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (b - a)).const_add z
    exact hk.comp_hasDerivAt (0 : ℝ) hl
  rw [hd.unique hg]
  simp only [f, zero_smul, sub_zero, one_smul]
  congr 1
  rw [sub_sub, add_sub_cancel]

end Profile

/-! ## The smeared segment as a form, and its pairing with closed forms -/

attribute [local instance] b3Forms_isManifold_real

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_tsupport_ofLoc [T2Space C] {k : ℕ} (x : C) {A : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hc : HasCompactSupport A) (hs : tsupport A ⊆ (chartAt E x).target) :
    tsupport (b3Rest_ofLoc x A) ⊆ (chartAt E x).symm '' tsupport A := by
  have hK : IsCompact ((chartAt E x).symm '' tsupport A) :=
    hc.isCompact.image_of_continuousOn ((chartAt E x).continuousOn_symm.mono hs)
  refine closure_minimal (fun p hp ↦ ?_) hK.isClosed
  by_cases hps : p ∈ (chartAt E x).source
  · have hA : A (chartAt E x p) ≠ 0 := by
      intro h0
      apply hp
      simp only [b3Rest_ofLoc, hps, ite_true, h0]
      ext v
      simp
    exact ⟨chartAt E x p, subset_closure hA, (chartAt E x).left_inv hps⟩
  · exact absurd (by simp [b3Rest_ofLoc, hps]) hp

/-- The field of the smeared segment from `a` to `b` in the chart at `x`. -/
def b3Rest_segField (hE : Module.finrank ℂ E = 1) (x : C) (ε : ℝ) (a b : ℂ) :
    E → E [⋀^Fin 1]→L[ℝ] ℝ := fun u ↦
  b3Rest_segK ε a b ((b3Rest_L hE).symm (u - chartAt E x x)) • b3Rest_iota hE (b - a)

/-- **The smeared segment** from `a` to `b` in the chart at `x`, a `1`-form on `C`. -/
def b3Rest_segForm (hE : Module.finrank ℂ E = 1) (x : C) (ε : ℝ) (a b : ℂ) :
    C → E [⋀^Fin 1]→L[ℝ] ℝ :=
  b3Rest_ofLoc x (b3Rest_segField hE x ε a b)

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_segField_props (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ} (hε : 0 < ε)
    (a b : ℂ) :
    ContDiff ℝ ∞ (b3Rest_segField hE x ε a b) ∧ HasCompactSupport (b3Rest_segField hE x ε a b) ∧
      tsupport (b3Rest_segField hE x ε a b) ⊆
        b3Rest_ζ hE x '' Metric.cthickening ε (segment ℝ a b) := by
  set ψ : E → ℂ := fun u ↦ (b3Rest_L hE).symm (u - chartAt E x x)
  have hψ : ContDiff ℝ ∞ ψ := (b3Rest_L hE).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hζψ : ∀ u, b3Rest_ζ hE x (ψ u) = u := fun u ↦ by
    show chartAt E x x + ψ u • b3Rest_e hE = u
    rw [← b3Rest_L_apply, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  have hζc : Continuous (b3Rest_ζ hE x) := by
    show Continuous fun z : ℂ ↦ chartAt E x x + z • b3Rest_e hE
    fun_prop
  have hK : IsCompact (Metric.cthickening ε (segment ℝ a b)) := by
    have hseg' : IsCompact (segment ℝ a b) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    exact hseg'.cthickening
  have hts : tsupport (b3Rest_segField hE x ε a b) ⊆
      b3Rest_ζ hE x '' Metric.cthickening ε (segment ℝ a b) := by
    refine closure_minimal (fun u hu ↦ ?_) (hK.image hζc).isClosed
    have : b3Rest_segK ε a b (ψ u) ≠ 0 := by
      intro h0
      apply hu
      show b3Rest_segK ε a b (ψ u) • b3Rest_iota hE (b - a) = 0
      rw [h0, zero_smul]
    refine ⟨ψ u, ?_, hζψ u⟩
    exact b3Rest_tsupport_segK hε a b (subset_closure this)
  refine ⟨(b3Rest_segK_contDiff ε a b).comp hψ |>.smul contDiff_const, ?_, hts⟩
  exact (hK.image hζc).of_isClosed_subset (isClosed_tsupport _) hts

theorem b3Rest_isSmooth_segForm [T2Space C] (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ}
    (hε : 0 < ε) {a b : ℂ}
    (hseg : ∀ z ∈ Metric.cthickening ε (segment ℝ a b), b3Rest_ζ hE x z ∈ (chartAt E x).target) :
    b3Forms_IsSmooth (b3Rest_segForm hE x ε a b) := by
  obtain ⟨h1, h2, h3⟩ := b3Rest_segField_props hE x hε a b
  exact b3Rest_isSmooth_ofLoc x h1 h2 (h3.trans (by rintro _ ⟨z, hz, rfl⟩; exact hseg z hz))

/-- A product supported in a compact subset of an open set, where the other factor is
continuous, is integrable. -/
theorem b3Rest_integrable_mul_of_tsupport {F G : ℂ → ℝ} {V : Set ℂ}
    (hG : Continuous G) (hGc : HasCompactSupport G) (hGV : tsupport G ⊆ V) (hF : ContinuousOn F V) :
    Integrable (fun z ↦ G z * F z) := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport G) ?_ fun z hz ↦ ?_
  · exact (hG.continuousOn.mul (hF.mono hGV)).integrableOn_compact hGc.isCompact
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

/-- **The pairing of a closed form with a smeared segment**: for a primitive `h` of `ω` on an
open set `U` of the chart image containing the `ε`-neighbourhood of the segment,
`∫ ω ∧ ι X = ∫ ρ_ε(w) h(b + w) dw - ∫ ρ_ε(w) h(a + w) dw`. -/
theorem b3Rest_integral_wedge_segForm (hE : Module.finrank ℂ E = 1)
    {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (x : C) {U : Set E} (hUo : IsOpen U)
    (hU : U ⊆ (chartAt E x).target) {h : E → ℝ}
    (hh : ∀ u ∈ U, HasFDerivAt h (b3Forms_toCLM (b3Forms_loc α x u)) u) {ε : ℝ} (hε : 0 < ε)
    {a b : ℂ} (hseg : ∀ z ∈ Metric.cthickening ε (segment ℝ a b), b3Rest_ζ hE x z ∈ U) :
    b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α (b3Rest_segForm hE x ε a b)) =
      (∫ w, b3Rest_rho ε w * h (b3Rest_ζ hE x (w + b))) -
        ∫ w, b3Rest_rho ε w * h (b3Rest_ζ hE x (w + a)) := by
  set c := chartAt E x x
  obtain ⟨hA, hAc, hAs⟩ := b3Rest_segField_props hE x hε a b
  have hAt : tsupport (b3Rest_segField hE x ε a b) ⊆ (chartAt E x).target :=
    hAs.trans (by rintro _ ⟨z, hz, rfl⟩; exact hU (hseg z hz))
  have hβ : b3Forms_IsSmooth (b3Rest_segForm hE x ε a b) :=
    b3Rest_isSmooth_ofLoc x hA hAc hAt
  have hζc : Continuous (b3Rest_ζ hE x) := by
    show Continuous fun z : ℂ ↦ c + z • b3Rest_e hE
    fun_prop
  have hsupp : tsupport (b3Forms_wedgeForm α (b3Rest_segForm hE x ε a b)) ⊆ (chartAt E x).source := by
    refine (closure_mono fun p hp ↦ ?_).trans ((b3Rest_tsupport_ofLoc x hAc hAt).trans ?_)
    · by_contra h0
      apply hp
      have h0' : b3Rest_segForm hE x ε a b p = 0 := Function.notMem_support.1 h0
      simp only [b3Forms_wedgeForm, h0', b3Rest_wedge_zero_right]
    · rintro _ ⟨u, hu, rfl⟩
      exact (chartAt E x).map_target (hAt hu)
  rw [b3Forms_integral_eq_chartIntegral _ b3Forms_oriented_complex (hα.wedgeForm hβ) hsupp,
    b3Forms_chartIntegral, b3Rest_integral_addHaar_eq hE _ c]
  set H : ℂ → ℝ := fun z ↦ h (b3Rest_ζ hE x z)
  set V : Set ℂ := b3Rest_ζ hE x ⁻¹' U
  have hVo : IsOpen V := hUo.preimage hζc
  have hKV : tsupport (b3Rest_segK ε a b) ⊆ V := fun z hz ↦
    hseg z (b3Rest_tsupport_segK hε a b hz)
  have hζd : ∀ z, HasFDerivAt (b3Rest_ζ hE x) ((b3Rest_L hE : ℂ →L[ℝ] E)) z := by
    intro z
    have := ((b3Rest_L hE : ℂ →L[ℝ] E).hasFDerivAt (x := z)).const_add c
    exact this
  have hHd : ∀ z ∈ V, HasFDerivAt H
      ((b3Forms_toCLM (b3Forms_loc α x (b3Rest_ζ hE x z))).comp (b3Rest_L hE : ℂ →L[ℝ] E)) z :=
    fun z hz ↦ (hh _ hz).comp z (hζd z)
  have hHc : ContinuousOn H V := fun z hz ↦ (hHd z hz).continuousAt.continuousWithinAt
  have hψζ : ∀ z, (b3Rest_L hE).symm (b3Rest_ζ hE x z - c) = z := b3Rest_L_symm_ζ hE x
  have hint_eq : ∀ z, b3Forms_chartFun (b3Rest_b hE) x
      (b3Forms_wedgeForm α (b3Rest_segForm hE x ε a b)) (c + z • b3Rest_e hE) =
        b3Rest_segK ε a b z * fderiv ℝ H z (b - a) := by
    intro z
    show b3Forms_chartFun (b3Rest_b hE) x _ (b3Rest_ζ hE x z) = _
    by_cases hz : z ∈ V
    · have ht : b3Rest_ζ hE x z ∈ (chartAt E x).target := hU hz
      rw [b3Forms_chartFun, indicator_of_mem ht, b3Forms_loc_wedgeForm]
      show b3Forms_wedge _ _ _ = _
      rw [b3Rest_segForm, b3Rest_loc_ofLoc_self x _ ht, b3Rest_segField, hψζ,
        b3Forms_wedge_smul_right]
      rw [ContinuousAlternatingMap.smul_apply, b3Rest_wedge_iota, (hHd z hz).fderiv]
      rfl
    · have h0 : b3Rest_segK ε a b z = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hz (hKV h')
      rw [h0, zero_mul, b3Forms_chartFun]
      by_cases ht : b3Rest_ζ hE x z ∈ (chartAt E x).target
      · rw [indicator_of_mem ht, b3Forms_loc_wedgeForm]
        show b3Forms_wedge _ _ _ = _
        rw [b3Rest_segForm, b3Rest_loc_ofLoc_self x _ ht, b3Rest_segField, hψζ, h0, zero_smul,
          b3Rest_wedge_zero_right]
        rfl
      · rw [indicator_of_notMem ht]
  simp only [hint_eq]
  have hsk := (b3Rest_segK_contDiff ε a b)
  have hskd : Differentiable ℝ (b3Rest_segK ε a b) := hsk.differentiable (by simp)
  have hfdc : ContinuousOn (fun z ↦ fderiv ℝ H z (b - a)) V := by
    have : EqOn (fun z ↦ fderiv ℝ H z (b - a)) (fun z ↦ b3Forms_loc α x (b3Rest_ζ hE x z)
        (fun _ ↦ b3Rest_L hE (b - a))) V := fun z hz ↦ by
      simp only [(hHd z hz).fderiv]
      rfl
    refine ContinuousOn.congr ?_ this
    have hl : ContinuousOn (fun z ↦ b3Forms_loc α x (b3Rest_ζ hE x z)) V :=
      ((hα x).continuousOn).comp hζc.continuousOn fun z hz ↦ hU hz
    exact (continuous_eval_const _).comp_continuousOn hl
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := b3Rest_segK ε a b) (g := H) (v := b - a)
    (b3Rest_integrable_mul_of_tsupport ((hsk.continuous_fderiv (by simp)).clm_apply continuous_const)
      ((b3Rest_hasCompactSupport_segK hε a b).fderiv_apply (𝕜 := ℝ) _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hKV) hHc)
    (b3Rest_integrable_mul_of_tsupport hsk.continuous (b3Rest_hasCompactSupport_segK hε a b) hKV
      hfdc)
    (b3Rest_integrable_mul_of_tsupport hsk.continuous (b3Rest_hasCompactSupport_segK hε a b) hKV
      hHc)
    (fun z _ ↦ hskd z) (fun z hz ↦ (hHd z (hKV hz)).differentiableAt)
  rw [hparts]
  simp only [b3Rest_fderiv_segK, sub_mul]
  have hρsub : ∀ p : ℂ, tsupport (fun z ↦ b3Rest_rho ε (z - p)) ⊆ closedBall p ε := by
    intro p
    refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
    by_contra hz'
    rw [mem_closedBall, dist_eq_norm, not_le] at hz'
    exact hz (b3Rest_rho_eq_zero hε hz'.le)
  have hρc : ∀ p : ℂ, p ∈ segment ℝ a b → Integrable (fun z ↦ b3Rest_rho ε (z - p) * H z) := by
    intro p hp
    refine b3Rest_integrable_mul_of_tsupport
      ((b3Rest_rho_contDiff ε).continuous.comp (continuous_id.sub continuous_const))
      ((isCompact_closedBall p ε).of_isClosed_subset (isClosed_tsupport _) (hρsub p))
      ((hρsub p).trans fun z hz ↦ hseg z ?_) hHc
    rw [← Metric.cthickening_singleton _ hε.le] at hz
    exact Metric.cthickening_subset_of_subset _ (singleton_subset_iff.2 hp) hz
  rw [integral_sub (hρc a (left_mem_segment ℝ a b)) (hρc b (right_mem_segment ℝ a b)), neg_sub]
  congr 1
  · rw [← integral_add_right_eq_self (fun z ↦ b3Rest_rho ε (z - b) * H z) b]
    simp only [add_sub_cancel_right, H]
  · rw [← integral_add_right_eq_self (fun z ↦ b3Rest_rho ε (z - a) * H z) a]
    simp only [add_sub_cancel_right, H]

end HodgeLean.Foundations.Program
