import HodgeLean.Foundations.Program.CurveJacobianRestSmear
import HodgeLean.Foundations.Program.CurveJacobianRestPoincare

/-! # Track B3, lane Rest: vector-field forms and junction corrections

In the chart at `x`, with complex coordinate `z`, a compactly supported smooth vector field
`(P, R)` gives the `1`-form `ι (P + R i)`. For a closed form `ω` with primitive `h` on a chart
region containing the support, `∫_C ω ∧ ι (P + R i) = -∫ (∂₁P + ∂_i R) h` (`b3Rest_integral_wedge_vecForm`;
two integrations by parts). With the planar Poincaré lemma this corrects the mismatch between
the bumps of two charts at a common point.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

/-- The field `ι (P + R i)` in the chart at `x`. -/
def b3Rest_vecField (hE : Module.finrank ℂ E = 1) (x : C) (P R : ℂ → ℝ) :
    E → E [⋀^Fin 1]→L[ℝ] ℝ := fun u ↦
  b3Rest_iota hE ((P ((b3Rest_L hE).symm (u - chartAt E x x)) : ℂ) +
    (R ((b3Rest_L hE).symm (u - chartAt E x x)) : ℂ) * Complex.I)

/-- **The vector-field form** `ι (P + R i)` in the chart at `x`. -/
def b3Rest_vecForm (hE : Module.finrank ℂ E = 1) (x : C) (P R : ℂ → ℝ) :
    C → E [⋀^Fin 1]→L[ℝ] ℝ :=
  b3Rest_ofLoc x (b3Rest_vecField hE x P R)

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_vecField_props (hE : Module.finrank ℂ E = 1) (x : C) {P R : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hR : ContDiff ℝ ∞ R) {K : Set ℂ} (hK : IsCompact K)
    (hPK : tsupport P ⊆ K) (hRK : tsupport R ⊆ K) :
    ContDiff ℝ ∞ (b3Rest_vecField hE x P R) ∧ HasCompactSupport (b3Rest_vecField hE x P R) ∧
      tsupport (b3Rest_vecField hE x P R) ⊆ b3Rest_ζ hE x '' K := by
  set ψ : E → ℂ := fun u ↦ (b3Rest_L hE).symm (u - chartAt E x x)
  have hψ : ContDiff ℝ ∞ ψ := (b3Rest_L hE).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hζψ : ∀ u, b3Rest_ζ hE x (ψ u) = u := fun u ↦ by
    show chartAt E x x + ψ u • b3Rest_e hE = u
    rw [← b3Rest_L_apply, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  have hζc : Continuous (b3Rest_ζ hE x) := by
    show Continuous fun z : ℂ ↦ chartAt E x x + z • b3Rest_e hE
    fun_prop
  have hts : tsupport (b3Rest_vecField hE x P R) ⊆ b3Rest_ζ hE x '' K := by
    refine closure_minimal (fun u hu ↦ ?_) (hK.image hζc).isClosed
    refine ⟨ψ u, ?_, hζψ u⟩
    by_contra hn
    apply hu
    have h1 : P (ψ u) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hn (hPK h)
    have h2 : R (ψ u) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hn (hRK h)
    show b3Rest_iota hE ((P (ψ u) : ℂ) + (R (ψ u) : ℂ) * Complex.I) = 0
    rw [h1, h2]
    simp
  refine ⟨?_, (hK.image hζc).of_isClosed_subset (isClosed_tsupport _) hts, hts⟩
  have h1 : ContDiff ℝ ∞ (fun u ↦ ((P (ψ u) : ℂ) + (R (ψ u) : ℂ) * Complex.I)) :=
    (Complex.ofRealCLM.contDiff.comp (hP.comp hψ)).add
      ((Complex.ofRealCLM.contDiff.comp (hR.comp hψ)).mul contDiff_const)
  exact (b3Rest_iota hE).contDiff.comp h1

/-- `A(L (p + r i)) = p A(L 1) + r A(L i)`. -/
theorem b3Rest_apply_L_add (hE : Module.finrank ℂ E = 1) (A : E →L[ℝ] ℝ) (p r : ℝ) :
    A (b3Rest_L hE ((p : ℂ) + (r : ℂ) * Complex.I)) =
      p * A (b3Rest_L hE 1) + r * A (b3Rest_L hE Complex.I) := by
  have : ((p : ℂ) + (r : ℂ) * Complex.I) = p • (1 : ℂ) + r • Complex.I := by
    simp [Complex.real_smul]
  rw [this, map_add, map_smul, map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 400000 in
/-- **The pairing of a closed form with a vector-field form**: for a primitive `h` of `ω` on an
open set `U` of the chart image containing the support,
`∫ ω ∧ ι (P + R i) = -∫ (∂₁P + ∂_i R)(z) h(z) dz`. -/
theorem b3Rest_integral_wedge_vecForm (hE : Module.finrank ℂ E = 1)
    {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (x : C) {U : Set E} (hUo : IsOpen U)
    (hU : U ⊆ (chartAt E x).target) {h : E → ℝ}
    (hh : ∀ u ∈ U, HasFDerivAt h (b3Forms_toCLM (b3Forms_loc α x u)) u) {P R : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hR : ContDiff ℝ ∞ R) {K : Set ℂ} (hK : IsCompact K)
    (hPK : tsupport P ⊆ K) (hRK : tsupport R ⊆ K) (hKU : ∀ z ∈ K, b3Rest_ζ hE x z ∈ U) :
    b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α (b3Rest_vecForm hE x P R)) =
      -∫ z, (fderiv ℝ P z 1 + fderiv ℝ R z Complex.I) * h (b3Rest_ζ hE x z) := by
  set c := chartAt E x x
  obtain ⟨hA, hAc, hAs⟩ := b3Rest_vecField_props hE x hP hR hK hPK hRK
  have hAt : tsupport (b3Rest_vecField hE x P R) ⊆ (chartAt E x).target :=
    hAs.trans (by rintro _ ⟨z, hz, rfl⟩; exact hU (hKU z hz))
  have hβ : b3Forms_IsSmooth (b3Rest_vecForm hE x P R) := b3Rest_isSmooth_ofLoc x hA hAc hAt
  have hζc : Continuous (b3Rest_ζ hE x) := by
    show Continuous fun z : ℂ ↦ c + z • b3Rest_e hE
    fun_prop
  have hsupp : tsupport (b3Forms_wedgeForm α (b3Rest_vecForm hE x P R)) ⊆
      (chartAt E x).source := by
    refine (closure_mono fun p hp ↦ ?_).trans ((b3Rest_tsupport_ofLoc x hAc hAt).trans ?_)
    · by_contra h0
      apply hp
      have h0' : b3Rest_vecForm hE x P R p = 0 := Function.notMem_support.1 h0
      simp only [b3Forms_wedgeForm, h0', b3Rest_wedge_zero_right]
    · rintro _ ⟨u, hu, rfl⟩
      exact (chartAt E x).map_target (hAt hu)
  rw [b3Forms_integral_eq_chartIntegral _ b3Forms_oriented_complex (hα.wedgeForm hβ) hsupp,
    b3Forms_chartIntegral, b3Rest_integral_addHaar_eq hE _ c]
  set H : ℂ → ℝ := fun z ↦ h (b3Rest_ζ hE x z)
  set V : Set ℂ := b3Rest_ζ hE x ⁻¹' U
  have hVo : IsOpen V := hUo.preimage hζc
  have hPV : tsupport P ⊆ V := fun z hz ↦ hKU z (hPK hz)
  have hRV : tsupport R ⊆ V := fun z hz ↦ hKU z (hRK hz)
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
      (b3Forms_wedgeForm α (b3Rest_vecForm hE x P R)) (c + z • b3Rest_e hE) =
        P z * fderiv ℝ H z 1 + R z * fderiv ℝ H z Complex.I := by
    intro z
    show b3Forms_chartFun (b3Rest_b hE) x _ (b3Rest_ζ hE x z) = _
    by_cases hz : z ∈ V
    · have ht : b3Rest_ζ hE x z ∈ (chartAt E x).target := hU hz
      rw [b3Forms_chartFun, indicator_of_mem ht, b3Forms_loc_wedgeForm]
      show b3Forms_wedge _ _ _ = _
      rw [b3Rest_vecForm, b3Rest_loc_ofLoc_self x _ ht, b3Rest_vecField, hψζ, b3Rest_wedge_iota,
        (hHd z hz).fderiv]
      have := b3Rest_apply_L_add hE (b3Forms_toCLM (b3Forms_loc α x (b3Rest_ζ hE x z))) (P z) (R z)
      simp only [b3Forms_toCLM_apply] at this
      rw [this]
      rfl
    · have h0 : P z = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hz (hPV h')
      have h0' : R z = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hz (hRV h')
      rw [h0, h0', zero_mul, zero_mul, add_zero, b3Forms_chartFun]
      by_cases ht : b3Rest_ζ hE x z ∈ (chartAt E x).target
      · rw [indicator_of_mem ht, b3Forms_loc_wedgeForm]
        show b3Forms_wedge _ _ _ = _
        rw [b3Rest_vecForm, b3Rest_loc_ofLoc_self x _ ht, b3Rest_vecField, hψζ, h0, h0']
        simp only [Complex.ofReal_zero, zero_mul, add_zero, _root_.map_zero, b3Rest_wedge_zero_right]
        rfl
      · rw [indicator_of_notMem ht]
  simp only [hint_eq]
  have hfdc : ∀ v : ℂ, ContinuousOn (fun z ↦ fderiv ℝ H z v) V := by
    intro v
    have : EqOn (fun z ↦ fderiv ℝ H z v) (fun z ↦ b3Forms_loc α x (b3Rest_ζ hE x z)
        (fun _ ↦ b3Rest_L hE v)) V := fun z hz ↦ by
      simp only [(hHd z hz).fderiv]
      rfl
    refine ContinuousOn.congr ?_ this
    have hl : ContinuousOn (fun z ↦ b3Forms_loc α x (b3Rest_ζ hE x z)) V :=
      ((hα x).continuousOn).comp hζc.continuousOn fun z hz ↦ hU hz
    exact (continuous_eval_const _).comp_continuousOn hl
  have hparts : ∀ (Q : ℂ → ℝ) (v : ℂ), ContDiff ℝ ∞ Q → HasCompactSupport Q → tsupport Q ⊆ V →
      ∫ z, Q z * fderiv ℝ H z v = -∫ z, fderiv ℝ Q z v * H z := by
    intro Q v hQ hQc hQV
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (b3Rest_integrable_mul_of_tsupport ((hQ.continuous_fderiv (by simp)).clm_apply
        continuous_const) (hQc.fderiv_apply (𝕜 := ℝ) _)
        ((tsupport_fderiv_apply_subset ℝ _).trans hQV) hHc)
      (b3Rest_integrable_mul_of_tsupport hQ.continuous hQc hQV (hfdc v))
      (b3Rest_integrable_mul_of_tsupport hQ.continuous hQc hQV hHc)
      (fun z _ ↦ (hQ.differentiable (by simp)) z) (fun z hz ↦ (hHd z (hQV hz)).differentiableAt)
  have hPc : HasCompactSupport P := hK.of_isClosed_subset (isClosed_tsupport _) hPK
  have hRc : HasCompactSupport R := hK.of_isClosed_subset (isClosed_tsupport _) hRK
  have hi1 : Integrable (fun z ↦ P z * fderiv ℝ H z 1) :=
    b3Rest_integrable_mul_of_tsupport hP.continuous hPc hPV (hfdc 1)
  have hi2 : Integrable (fun z ↦ R z * fderiv ℝ H z Complex.I) :=
    b3Rest_integrable_mul_of_tsupport hR.continuous hRc hRV (hfdc Complex.I)
  have hj1 : Integrable (fun z ↦ fderiv ℝ P z 1 * H z) :=
    b3Rest_integrable_mul_of_tsupport ((hP.continuous_fderiv (by simp)).clm_apply
      continuous_const) (hPc.fderiv_apply (𝕜 := ℝ) _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hPV) hHc
  have hj2 : Integrable (fun z ↦ fderiv ℝ R z Complex.I * H z) :=
    b3Rest_integrable_mul_of_tsupport ((hR.continuous_fderiv (by simp)).clm_apply
      continuous_const) (hRc.fderiv_apply (𝕜 := ℝ) _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hRV) hHc
  rw [integral_add hi1 hi2, hparts P 1 hP hPc hPV, hparts R Complex.I hR hRc hRV, ← neg_add,
    ← integral_add hj1 hj2]
  simp only [add_mul, H]

/-! ## Bump `2`-forms -/

/-- The area form with value `1` on `(e, i e)`. -/
def b3Rest_vol (hE : Module.finrank ℂ E = 1) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  b3Forms_wedge (b3Rest_iota hE Complex.I) (b3Rest_iota hE (-1))

theorem b3Rest_vol_b (hE : Module.finrank ℂ E = 1) : b3Rest_vol hE (b3Rest_b hE) = 1 := by
  rw [b3Rest_vol, b3Rest_wedge_iota, b3Rest_iota_apply, ContinuousLinearEquiv.symm_apply_apply]
  simp

/-- The complex coordinate of a point of the chart at `x`. -/
def b3Rest_pt (hE : Module.finrank ℂ E = 1) (x w : C) : ℂ :=
  (b3Rest_L hE).symm (chartAt E x w - chartAt E x x)

omit [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] in
theorem b3Rest_ζ_pt (hE : Module.finrank ℂ E = 1) (x w : C) :
    b3Rest_ζ hE x (b3Rest_pt hE x w) = chartAt E x w := by
  show chartAt E x x + b3Rest_pt hE x w • b3Rest_e hE = _
  rw [← b3Rest_L_apply, b3Rest_pt, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]

omit [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] in
theorem b3Rest_ζ_L_symm (hE : Module.finrank ℂ E = 1) (x : C) (u : E) :
    b3Rest_ζ hE x ((b3Rest_L hE).symm (u - chartAt E x x)) = u := by
  show chartAt E x x + _ • b3Rest_e hE = u
  rw [← b3Rest_L_apply, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]

omit [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] in
theorem b3Rest_continuous_ζ (hE : Module.finrank ℂ E = 1) (x : C) :
    Continuous (b3Rest_ζ hE x) := by
  show Continuous fun z : ℂ ↦ chartAt E x x + z • b3Rest_e hE
  fun_prop

/-- The bump field `ρ_ε(z - p) vol` in the chart at `x`. -/
def b3Rest_bumpField (hE : Module.finrank ℂ E = 1) (x : C) (ε : ℝ) (p : ℂ) :
    E → E [⋀^Fin 2]→L[ℝ] ℝ := fun u ↦
  b3Rest_rho ε ((b3Rest_L hE).symm (u - chartAt E x x) - p) • b3Rest_vol hE

/-- **The bump `2`-form** `ρ_ε(z - p) dx ∧ dy` in the chart at `x`. -/
def b3Rest_bumpForm (hE : Module.finrank ℂ E = 1) (x : C) (ε : ℝ) (p : ℂ) :
    C → E [⋀^Fin 2]→L[ℝ] ℝ :=
  b3Rest_ofLoc x (b3Rest_bumpField hE x ε p)

theorem b3Rest_tsupport_rho_sub {ε : ℝ} (hε : 0 < ε) (p : ℂ) :
    tsupport (fun z ↦ b3Rest_rho ε (z - p)) ⊆ closedBall p ε := by
  refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
  by_contra hz'
  rw [mem_closedBall, dist_eq_norm, not_le] at hz'
  exact hz (b3Rest_rho_eq_zero hε hz'.le)

omit [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] in
theorem b3Rest_bumpField_props (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ} (hε : 0 < ε)
    (p : ℂ) :
    ContDiff ℝ ∞ (b3Rest_bumpField hE x ε p) ∧ HasCompactSupport (b3Rest_bumpField hE x ε p) ∧
      tsupport (b3Rest_bumpField hE x ε p) ⊆ b3Rest_ζ hE x '' closedBall p ε := by
  set ψ : E → ℂ := fun u ↦ (b3Rest_L hE).symm (u - chartAt E x x)
  have hψ : ContDiff ℝ ∞ ψ := (b3Rest_L hE).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hK : IsCompact (b3Rest_ζ hE x '' closedBall p ε) :=
    (isCompact_closedBall p ε).image (b3Rest_continuous_ζ hE x)
  have hts : tsupport (b3Rest_bumpField hE x ε p) ⊆ b3Rest_ζ hE x '' closedBall p ε := by
    refine closure_minimal (fun u hu ↦ ?_) hK.isClosed
    refine ⟨ψ u, ?_, b3Rest_ζ_L_symm hE x u⟩
    by_contra hn
    apply hu
    rw [mem_closedBall, dist_eq_norm, not_le] at hn
    show b3Rest_rho ε (ψ u - p) • b3Rest_vol hE = 0
    rw [b3Rest_rho_eq_zero hε hn.le, zero_smul]
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts⟩
  exact ((b3Rest_rho_contDiff ε).comp (hψ.sub contDiff_const)).smul contDiff_const

theorem b3Rest_chartFun_smulFun (b : Module.Basis (Fin 2) ℝ E) (y : C) (G : C → ℝ)
    (β : C → E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) :
    b3Forms_chartFun b y (b3Forms_smulFun G β) u =
      G ((chartAt E y).symm u) * b3Forms_chartFun b y β u := by
  by_cases hu : u ∈ (chartAt E y).target
  · rw [b3Forms_chartFun, b3Forms_chartFun, indicator_of_mem hu, indicator_of_mem hu,
      b3Forms_loc_smulFun]
    rfl
  · rw [b3Forms_chartFun, b3Forms_chartFun, indicator_of_notMem hu, indicator_of_notMem hu,
      mul_zero]

theorem b3Rest_chartFun_bumpForm (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ} (hε : 0 < ε)
    (p : ℂ) (hp : ∀ z ∈ closedBall p ε, b3Rest_ζ hE x z ∈ (chartAt E x).target) (z : ℂ) :
    b3Forms_chartFun (b3Rest_b hE) x (b3Rest_bumpForm hE x ε p) (b3Rest_ζ hE x z) =
      b3Rest_rho ε (z - p) := by
  by_cases ht : b3Rest_ζ hE x z ∈ (chartAt E x).target
  · rw [b3Forms_chartFun, indicator_of_mem ht, b3Rest_bumpForm, b3Rest_loc_ofLoc_self x _ ht,
      b3Rest_bumpField, b3Rest_L_symm_ζ, ContinuousAlternatingMap.smul_apply, b3Rest_vol_b,
      smul_eq_mul, mul_one]
  · have hz : z ∉ closedBall p ε := fun h ↦ ht (hp z h)
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    rw [b3Forms_chartFun, indicator_of_notMem ht, b3Rest_rho_eq_zero hε hz.le]

theorem b3Rest_tsupport_bumpForm (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ} (hε : 0 < ε)
    (p : ℂ) (hp : ∀ z ∈ closedBall p ε, b3Rest_ζ hE x z ∈ (chartAt E x).target) :
    tsupport (b3Rest_bumpForm hE x ε p) ⊆
      (chartAt E x).symm '' (b3Rest_ζ hE x '' closedBall p ε) := by
  obtain ⟨_, hAc, hAs⟩ := b3Rest_bumpField_props hE x hε p
  have hAt : tsupport (b3Rest_bumpField hE x ε p) ⊆ (chartAt E x).target :=
    hAs.trans (by rintro _ ⟨z, hz, rfl⟩; exact hp z hz)
  exact (b3Rest_tsupport_ofLoc x hAc hAt).trans (image_mono hAs)

theorem b3Rest_isSmooth_bumpForm (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ} (hε : 0 < ε)
    (p : ℂ) (hp : ∀ z ∈ closedBall p ε, b3Rest_ζ hE x z ∈ (chartAt E x).target) :
    b3Forms_IsSmooth (b3Rest_bumpForm hE x ε p) := by
  obtain ⟨hA, hAc, hAs⟩ := b3Rest_bumpField_props hE x hε p
  exact b3Rest_isSmooth_ofLoc x hA hAc (hAs.trans (by rintro _ ⟨z, hz, rfl⟩; exact hp z hz))

/-- The density of a smooth `2`-form supported in a chart domain is smooth in the complex
coordinate. -/
theorem b3Rest_contDiff_chartFun (hE : Module.finrank ℂ E = 1)
    {β : C → E [⋀^Fin 2]→L[ℝ] ℝ} (hβ : b3Forms_IsSmooth β) {y : C}
    (hy : tsupport β ⊆ (chartAt E y).source) :
    ContDiff ℝ ∞ (fun z ↦ b3Forms_chartFun (b3Rest_b hE) y β (b3Rest_ζ hE y z)) := by
  have hζ : ContDiff ℝ ∞ (b3Rest_ζ hE y) := contDiff_const.add (contDiff_id.smul contDiff_const)
  refine ContDiff.comp ?_ hζ
  obtain ⟨hsub, hK⟩ := b3Forms_tsupport_chartFun_subset (b3Rest_b hE)
    (b3Forms_isCompact_tsupport β) hy
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ (chartAt E y).target
  · have he : b3Forms_chartFun (b3Rest_b hE) y β =ᶠ[𝓝 u]
        fun v ↦ ContinuousAlternatingMap.apply ℝ E ℝ (b3Rest_b hE) (b3Forms_loc β y v) := by
      filter_upwards [(chartAt E y).open_target.mem_nhds hu] with v hv
      rw [b3Forms_chartFun, indicator_of_mem hv]
      rfl
    refine ContDiffAt.congr_of_eventuallyEq ?_ he
    exact (ContinuousAlternatingMap.apply ℝ E ℝ (b3Rest_b hE)).contDiff.contDiffAt.comp u
      ((hβ y).contDiffAt ((chartAt E y).open_target.mem_nhds hu))
  · have hu' : u ∉ tsupport (b3Forms_chartFun (b3Rest_b hE) y β) := by
      intro h
      obtain ⟨c, hc, rfl⟩ := hsub h
      exact hu ((chartAt E y).map_source (hy hc))
    have he : b3Forms_chartFun (b3Rest_b hE) y β =ᶠ[𝓝 u] fun _ ↦ 0 :=
      notMem_tsupport_iff_eventuallyEq.1 hu'
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- `ρ_ε` has positive mass. -/
theorem b3Rest_integral_rho_pos {ε : ℝ} (hε : 0 < ε) : 0 < ∫ z, b3Rest_rho ε z := by
  have hc : Continuous (b3Rest_rho ε) := (b3Rest_rho_contDiff ε).continuous
  have hcs : HasCompactSupport (b3Rest_rho ε) :=
    (isCompact_closedBall (0 : ℂ) ε).of_isClosed_subset (isClosed_tsupport _)
      (by simpa using b3Rest_tsupport_rho_sub hε 0)
  have h0 : b3Rest_rho ε 0 ≠ 0 := by
    show b3Rest_bump (ε⁻¹ • (0 : ℂ)) ≠ 0
    rw [smul_zero]
    exact (b3Rest_bump_pos (by simp)).ne'
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (b3Rest_rho_nonneg ε) h0

/-- Two primitives of a closed form in two charts differ by a constant on a disc of the
overlap. -/
theorem b3Rest_primitive_const (hE : Module.finrank ℂ E = 1) {α : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    {x y : C} {Ux Uy : Set E} {hx hy : E → ℝ}
    (hhx : ∀ u ∈ Ux, HasFDerivAt hx (b3Forms_toCLM (b3Forms_loc α x u)) u)
    (hhy : ∀ u ∈ Uy, HasFDerivAt hy (b3Forms_toCLM (b3Forms_loc α y u)) u) {q : ℂ} {δ : ℝ}
    (hW : ∀ z ∈ ball q δ, b3Rest_ζ hE y z ∈ Uy ∧ b3Rest_ζ hE y z ∈ b3Forms_trDom y x ∧
      b3Forms_tr y x (b3Rest_ζ hE y z) ∈ Ux) {z z' : ℂ} (hz : z ∈ ball q δ)
    (hz' : z' ∈ ball q δ) :
    hx (b3Forms_tr y x (b3Rest_ζ hE y z)) - hy (b3Rest_ζ hE y z) =
      hx (b3Forms_tr y x (b3Rest_ζ hE y z')) - hy (b3Rest_ζ hE y z') := by
  set g : ℂ → ℝ := fun z ↦ hx (b3Forms_tr y x (b3Rest_ζ hE y z)) - hy (b3Rest_ζ hE y z)
  have hg : ∀ z ∈ ball q δ, HasFDerivAt g (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hW z hz
    have hζd : HasFDerivAt (b3Rest_ζ hE y) (b3Rest_L hE : ℂ →L[ℝ] E) z :=
      ((b3Rest_L hE : ℂ →L[ℝ] E).hasFDerivAt (x := z)).const_add _
    have ha : HasFDerivAt (fun u ↦ hx (b3Forms_tr y x u) - hy u) (0 : E →L[ℝ] ℝ)
        (b3Rest_ζ hE y z) := by
      have := ((hhx _ h3).comp _ (b3Forms_differentiableAt_tr h2).hasFDerivAt).sub (hhy _ h1)
      refine this.congr_fderiv ?_
      rw [b3Forms_loc_eq_comp α h2]
      ext v
      simp only [_root_.zero_apply, _root_.sub_apply,
        ContinuousLinearMap.comp_apply, b3Forms_toCLM_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact sub_self _
    have := ha.comp z hζd
    rw [ContinuousLinearMap.zero_comp] at this
    exact this
  have hgd : DifferentiableOn ℝ g (ball q δ) := fun z hz ↦
    (hg z hz).differentiableAt.differentiableWithinAt
  exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball q δ).isPreconnected hgd
    (fun z hz ↦ (hg z hz).fderiv) hz hz'

set_option maxHeartbeats 400000 in
/-- **The junction correction**: at a point `w` of two charts, for `ε` small there is a smooth
`1`-form `κ` such that for every closed form with primitives `h_x`, `h_y` on neighbourhoods of `w`
in the two charts, `∫ ω ∧ κ` is the difference of the `ρ_ε`-averages of `h_y` and `h_x` at `w`
plus `(∫ ρ_ε) (h_x(w) - h_y(w))`. -/
theorem b3Rest_junction (hE : Module.finrank ℂ E = 1) {x y w : C}
    (hwx : w ∈ (chartAt E x).source) (hwy : w ∈ (chartAt E y).source) {Ux Uy : Set E}
    (hUxo : IsOpen Ux) (hUyo : IsOpen Uy) (hUx : Ux ⊆ (chartAt E x).target)
    (hUy : Uy ⊆ (chartAt E y).target) (hwUx : chartAt E x w ∈ Ux) (hwUy : chartAt E y w ∈ Uy) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∃ κ : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth κ ∧
      tsupport κ ⊆ (chartAt E y).symm '' Uy ∧
      ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → ∀ hx hy : E → ℝ,
        (∀ u ∈ Ux, HasFDerivAt hx (b3Forms_toCLM (b3Forms_loc α x u)) u) →
        (∀ u ∈ Uy, HasFDerivAt hy (b3Forms_toCLM (b3Forms_loc α y u)) u) →
        b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α κ) =
          (∫ z, b3Rest_rho ε z * hy (b3Rest_ζ hE y (z + b3Rest_pt hE y w))) -
            (∫ z, b3Rest_rho ε z * hx (b3Rest_ζ hE x (z + b3Rest_pt hE x w))) +
            (∫ z, b3Rest_rho ε z) * (hx (chartAt E x w) - hy (chartAt E y w)) := by
  set p := b3Rest_pt hE x w
  set q := b3Rest_pt hE y w
  have hζp : b3Rest_ζ hE x p = chartAt E x w := b3Rest_ζ_pt hE x w
  have hζq : b3Rest_ζ hE y q = chartAt E y w := b3Rest_ζ_pt hE y w
  have htr : b3Forms_tr y x (chartAt E y w) = chartAt E x w := by
    show chartAt E x ((chartAt E y).symm (chartAt E y w)) = _
    rw [(chartAt E y).left_inv hwy]
  -- the disc of the overlap
  have hWo : IsOpen {z : ℂ | b3Rest_ζ hE y z ∈ Uy ∧ b3Rest_ζ hE y z ∈ b3Forms_trDom y x ∧
      b3Forms_tr y x (b3Rest_ζ hE y z) ∈ Ux} := by
    have h1 : IsOpen (Uy ∩ (b3Forms_trDom (E := E) y x ∩ b3Forms_tr y x ⁻¹' Ux)) :=
      hUyo.inter (ContinuousOn.isOpen_inter_preimage
        (fun u hu ↦ (b3Forms_differentiableAt_tr hu).continuousAt.continuousWithinAt)
        (b3Forms_isOpen_trDom y x) hUxo)
    exact h1.preimage (b3Rest_continuous_ζ hE y)
  have hqW : b3Rest_ζ hE y q ∈ Uy ∧ b3Rest_ζ hE y q ∈ b3Forms_trDom y x ∧
      b3Forms_tr y x (b3Rest_ζ hE y q) ∈ Ux := by
    rw [hζq, htr]
    refine ⟨hwUy, ⟨(chartAt E y).map_source hwy, ?_⟩, hwUx⟩
    show (chartAt E y).symm (chartAt E y w) ∈ (chartAt E x).source
    rw [(chartAt E y).left_inv hwy]
    exact hwx
  obtain ⟨δ₃, hδ₃, hδ₃W⟩ := Metric.isOpen_iff.1 hWo q hqW
  set δ := δ₃ / 3
  have hδ3 : δ = δ₃ / 3 := rfl
  have hδ : 0 < δ := by positivity
  -- the change of chart in complex coordinates
  set Φ : ℂ → ℂ := fun z ↦ (b3Rest_L hE).symm
    (chartAt E y ((chartAt E x).symm (b3Rest_ζ hE x z)) - chartAt E y y)
  have hΦp : Φ p = q := by
    simp only [Φ, hζp, (chartAt E x).left_inv hwx]
    rfl
  have hΦc : ∀ z, b3Rest_ζ hE x z ∈ (chartAt E x).target →
      (chartAt E x).symm (b3Rest_ζ hE x z) ∈ (chartAt E y).source → ContinuousAt Φ z := by
    intro z h1 h2
    refine (b3Rest_L hE).symm.continuous.continuousAt.comp ?_
    refine ContinuousAt.sub ?_ continuousAt_const
    exact ContinuousAt.comp (g := chartAt E y)
      (f := fun z ↦ (chartAt E x).symm (b3Rest_ζ hE x z)) ((chartAt E y).continuousAt h2)
      (((chartAt E x).continuousAt_symm h1).comp (b3Rest_continuous_ζ hE x).continuousAt)
  have hpt0 : b3Rest_ζ hE x p ∈ (chartAt E x).target := hUx (hζp ▸ hwUx)
  have hps0 : (chartAt E x).symm (b3Rest_ζ hE x p) ∈ (chartAt E y).source := by
    rw [hζp, (chartAt E x).left_inv hwx]
    exact hwy
  have hev : ∀ᶠ z in 𝓝 p, b3Rest_ζ hE x z ∈ Ux ∧
      (chartAt E x).symm (b3Rest_ζ hE x z) ∈ (chartAt E y).source ∧ Φ z ∈ ball q δ := by
    have e1 : ∀ᶠ z in 𝓝 p, b3Rest_ζ hE x z ∈ Ux :=
      (b3Rest_continuous_ζ hE x).continuousAt.preimage_mem_nhds (hUxo.mem_nhds (hζp ▸ hwUx))
    have e2 : ∀ᶠ z in 𝓝 p, (chartAt E x).symm (b3Rest_ζ hE x z) ∈ (chartAt E y).source :=
      (((chartAt E x).continuousAt_symm hpt0).comp
        (b3Rest_continuous_ζ hE x).continuousAt).preimage_mem_nhds
        ((chartAt E y).open_source.mem_nhds hps0)
    have e3 : ∀ᶠ z in 𝓝 p, Φ z ∈ ball q δ :=
      (hΦc p hpt0 hps0).preimage_mem_nhds (hΦp ▸ ball_mem_nhds _ hδ)
    exact e1.and (e2.and e3)
  obtain ⟨ε₁, hε₁, hε₁p⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min (ε₁ / 2) δ, lt_min (half_pos hε₁) hδ, fun ε hε hεlt ↦ ?_⟩
  have hεδ : ε < δ := hεlt.trans_le (min_le_right _ _)
  have hball : ∀ z ∈ closedBall p ε, z ∈ ball p ε₁ := fun z hz ↦ by
    rw [mem_ball]
    rw [mem_closedBall] at hz
    linarith [min_le_left (ε₁ / 2) δ]
  have hpt : ∀ z ∈ closedBall p ε, b3Rest_ζ hE x z ∈ (chartAt E x).target :=
    fun z hz ↦ hUx (hε₁p z (hball z hz)).1
  -- the bump in the chart at `x`
  set μ := b3Rest_bumpForm hE x ε p
  have hμ : b3Forms_IsSmooth μ := b3Rest_isSmooth_bumpForm hE x hε p hpt
  have hμS := b3Rest_tsupport_bumpForm hE x hε p hpt
  have hμx : tsupport μ ⊆ (chartAt E x).source := hμS.trans (by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact (chartAt E x).map_target (hpt z hz))
  have hμy : tsupport μ ⊆ (chartAt E y).source := hμS.trans (by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact (hε₁p z (hball z hz)).2.1)
  -- its density in the chart at `y`
  set dens : ℂ → ℝ := fun z ↦ b3Forms_chartFun (b3Rest_b hE) y μ (b3Rest_ζ hE y z)
  have hdens : ContDiff ℝ ∞ dens := b3Rest_contDiff_chartFun hE hμ hμy
  have hΦK : IsCompact (Φ '' closedBall p ε) :=
    (isCompact_closedBall p ε).image_of_continuousOn fun z hz ↦
      (hΦc z (hpt z hz) (hε₁p z (hball z hz)).2.1).continuousWithinAt
  have hdensS : tsupport dens ⊆ Φ '' closedBall p ε := by
    refine closure_minimal (fun z hz ↦ ?_) hΦK.isClosed
    obtain ⟨c, ⟨_, hcμ⟩, hc⟩ := b3Forms_support_chartFun_subset (b3Rest_b hE) y μ hz
    obtain ⟨_, ⟨z', hz', rfl⟩, rfl⟩ := hμS (subset_tsupport _ hcμ)
    refine ⟨z', hz', ?_⟩
    show (b3Rest_L hE).symm (chartAt E y ((chartAt E x).symm (b3Rest_ζ hE x z')) -
      chartAt E y y) = z
    rw [hc, b3Rest_L_symm_ζ]
  have hΦδ : Φ '' closedBall p ε ⊆ ball q δ := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hε₁p z (hball z hz)).2.2
  -- the zero-mass difference
  set f : ℂ → ℝ := fun z ↦ dens z - b3Rest_rho ε (z - q)
  have hρq : ContDiff ℝ ∞ (fun z ↦ b3Rest_rho ε (z - q)) :=
    (b3Rest_rho_contDiff ε).comp (contDiff_id.sub contDiff_const)
  have hf : ContDiff ℝ ∞ f := hdens.sub hρq
  have hfS : tsupport f ⊆ ball q δ :=
    (tsupport_sub _ _).trans (union_subset (hdensS.trans hΦδ)
      ((b3Rest_tsupport_rho_sub hε q).trans (closedBall_subset_ball hεδ)))
  have hdensc : HasCompactSupport dens := hΦK.of_isClosed_subset (isClosed_tsupport _) hdensS
  have hρqc : HasCompactSupport (fun z ↦ b3Rest_rho ε (z - q)) :=
    (isCompact_closedBall q ε).of_isClosed_subset (isClosed_tsupport _)
      (b3Rest_tsupport_rho_sub hε q)
  have hmass : ∀ r : ℂ, ∫ z, b3Rest_rho ε (z - r) = ∫ z, b3Rest_rho ε z :=
    fun r ↦ integral_sub_right_eq_self (fun z ↦ b3Rest_rho ε z) r
  have hdensI : ∀ G : C → ℝ, ∫ z, dens z * G ((chartAt E y).symm (b3Rest_ζ hE y z)) =
      ∫ z, b3Rest_rho ε (z - p) * G ((chartAt E x).symm (b3Rest_ζ hE x z)) := by
    intro G
    have h1 := b3Rest_integral_addHaar_eq hE
      (b3Forms_chartFun (b3Rest_b hE) y (b3Forms_smulFun G μ)) (chartAt E y y)
    have h2 := b3Rest_integral_addHaar_eq hE
      (b3Forms_chartFun (b3Rest_b hE) x (b3Forms_smulFun G μ)) (chartAt E x x)
    have h3 := b3Forms_chartIntegral_eq_of_tsupport_subset (b3Rest_b hE) b3Forms_oriented_complex
      ((b3Forms_tsupport_smulFun_subset_right G μ).trans hμx)
      ((b3Forms_tsupport_smulFun_subset_right G μ).trans hμy)
    rw [b3Forms_chartIntegral, b3Forms_chartIntegral, h1, h2] at h3
    simp only [b3Rest_chartFun_smulFun] at h3
    have h4 : ∀ z, b3Forms_chartFun (b3Rest_b hE) x μ (chartAt E x x + z • b3Rest_e hE) =
        b3Rest_rho ε (z - p) := b3Rest_chartFun_bumpForm hE x hε p hpt
    simp only [h4] at h3
    have h5 : ∫ z, dens z * G ((chartAt E y).symm (b3Rest_ζ hE y z)) =
        ∫ z : ℂ, G ((chartAt E y).symm (chartAt E y y + z • b3Rest_e hE)) *
          b3Forms_chartFun (b3Rest_b hE) y μ (chartAt E y y + z • b3Rest_e hE) := by
      congr 1
      funext z
      rw [mul_comm]
      rfl
    have h6 : ∫ z : ℂ, G ((chartAt E x).symm (chartAt E x x + z • b3Rest_e hE)) *
          b3Rest_rho ε (z - p) =
        ∫ z, b3Rest_rho ε (z - p) * G ((chartAt E x).symm (b3Rest_ζ hE x z)) := by
      congr 1
      funext z
      rw [mul_comm]
      rfl
    rw [h5, ← h3, h6]
  have h0 : ∫ z, f z = 0 := by
    have := hdensI (fun _ ↦ 1)
    simp only [mul_one] at this
    rw [integral_sub (hdens.continuous.integrable_of_hasCompactSupport hdensc)
      (hρq.continuous.integrable_of_hasCompactSupport hρqc), this, hmass, hmass, sub_self]
  obtain ⟨P, R, hP, hR, hPs, hRs, hdiv⟩ := b3Rest_poincare hf hδ hfS h0
  have hKW : ∀ z ∈ closedBall q (2 * δ), z ∈ ball q δ₃ := fun z hz ↦ by
    rw [mem_ball]
    rw [mem_closedBall] at hz
    linarith
  obtain ⟨hA, hAc, hAs⟩ := b3Rest_vecField_props hE y hP hR (isCompact_closedBall q (2 * δ))
    hPs hRs
  have hAt : tsupport (b3Rest_vecField hE y P R) ⊆ (chartAt E y).target := hAs.trans (by
    rintro _ ⟨z, hz, rfl⟩
    exact hUy (hδ₃W (hKW z hz)).1)
  refine ⟨b3Rest_vecForm hE y P R, b3Rest_isSmooth_ofLoc y hA hAc hAt,
    ((b3Rest_tsupport_ofLoc y hAc hAt).trans (image_mono (hAs.trans ?_))),
    fun α hα hx hy hhx hhy ↦ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hδ₃W (hKW z hz)).1
  rw [b3Rest_integral_wedge_vecForm hE hα y hUyo hUy hhy hP hR (isCompact_closedBall q (2 * δ))
    hPs hRs (fun z hz ↦ (hδ₃W (hKW z hz)).1)]
  simp only [hdiv]
  -- the primitives along the two charts
  have hHy : ContinuousOn (fun z ↦ hy (b3Rest_ζ hE y z)) (b3Rest_ζ hE y ⁻¹' Uy) := fun z hz ↦
    ((hhy _ hz).continuousAt.comp (b3Rest_continuous_ζ hE y).continuousAt).continuousWithinAt
  have hHx : ContinuousOn (fun z ↦ hx (b3Rest_ζ hE x z)) (b3Rest_ζ hE x ⁻¹' Ux) := fun z hz ↦
    ((hhx _ hz).continuousAt.comp (b3Rest_continuous_ζ hE x).continuousAt).continuousWithinAt
  have hδV : ball q δ ⊆ b3Rest_ζ hE y ⁻¹' Uy := fun z hz ↦
    (hδ₃W (ball_subset_ball (by linarith) hz)).1
  have hi1 : Integrable (fun z ↦ dens z * hy (b3Rest_ζ hE y z)) :=
    b3Rest_integrable_mul_of_tsupport hdens.continuous hdensc ((hdensS.trans hΦδ).trans hδV) hHy
  have hi2 : Integrable (fun z ↦ b3Rest_rho ε (z - q) * hy (b3Rest_ζ hE y z)) :=
    b3Rest_integrable_mul_of_tsupport hρq.continuous hρqc
      (((b3Rest_tsupport_rho_sub hε q).trans (closedBall_subset_ball hεδ)).trans hδV) hHy
  have hpV : closedBall p ε ⊆ b3Rest_ζ hE x ⁻¹' Ux := fun z hz ↦ (hε₁p z (hball z hz)).1
  have hρp : ContDiff ℝ ∞ (fun z ↦ b3Rest_rho ε (z - p)) :=
    (b3Rest_rho_contDiff ε).comp (contDiff_id.sub contDiff_const)
  have hρpc : HasCompactSupport (fun z ↦ b3Rest_rho ε (z - p)) :=
    (isCompact_closedBall p ε).of_isClosed_subset (isClosed_tsupport _)
      (b3Rest_tsupport_rho_sub hε p)
  have hi3 : Integrable (fun z ↦ b3Rest_rho ε (z - p) * hx (b3Rest_ζ hE x z)) :=
    b3Rest_integrable_mul_of_tsupport hρp.continuous hρpc
      ((b3Rest_tsupport_rho_sub hε p).trans hpV) hHx
  set C₀ := hx (chartAt E x w) - hy (chartAt E y w)
  -- the density term, read in the chart at `x`
  have hD : ∫ z, dens z * hy (b3Rest_ζ hE y z) =
      (∫ z, b3Rest_rho ε (z - p) * hx (b3Rest_ζ hE x z)) - C₀ * ∫ z, b3Rest_rho ε z := by
    have e1 : ∫ z, dens z * hy (b3Rest_ζ hE y z) =
        ∫ z, dens z * (fun c ↦ hy (chartAt E y c)) ((chartAt E y).symm (b3Rest_ζ hE y z)) := by
      congr 1
      funext z
      by_cases ht : b3Rest_ζ hE y z ∈ (chartAt E y).target
      · show _ = dens z * hy (chartAt E y ((chartAt E y).symm (b3Rest_ζ hE y z)))
        rw [(chartAt E y).right_inv ht]
      · have : dens z = 0 := by
          show b3Forms_chartFun (b3Rest_b hE) y μ (b3Rest_ζ hE y z) = 0
          rw [b3Forms_chartFun, indicator_of_notMem ht]
        rw [this, zero_mul, zero_mul]
    rw [e1, hdensI (fun c ↦ hy (chartAt E y c)), ← hmass p, ← integral_const_mul, ← integral_sub hi3
      ((hρp.continuous.integrable_of_hasCompactSupport hρpc).const_mul C₀)]
    congr 1
    funext z
    by_cases hz : z ∈ closedBall p ε
    · obtain ⟨h1, h2, h3⟩ := hε₁p z (hball z hz)
      have hz1 : Φ z ∈ ball q δ₃ := ball_subset_ball (by linarith) h3
      have hc := b3Rest_primitive_const hE hhx hhy hδ₃W hz1 (mem_ball_self hδ₃)
      have hζΦ : b3Rest_ζ hE y (Φ z) = chartAt E y ((chartAt E x).symm (b3Rest_ζ hE x z)) :=
        b3Rest_ζ_L_symm hE y _
      have htrΦ : b3Forms_tr y x (b3Rest_ζ hE y (Φ z)) = b3Rest_ζ hE x z := by
        rw [hζΦ]
        show chartAt E x ((chartAt E y).symm (chartAt E y ((chartAt E x).symm _))) = _
        rw [(chartAt E y).left_inv h2, (chartAt E x).right_inv (hUx h1)]
      rw [htrΦ, hζΦ, hζq, htr] at hc
      show b3Rest_rho ε (z - p) * hy (chartAt E y ((chartAt E x).symm (b3Rest_ζ hE x z))) =
        b3Rest_rho ε (z - p) * hx (b3Rest_ζ hE x z) - C₀ * b3Rest_rho ε (z - p)
      have : hy (chartAt E y ((chartAt E x).symm (b3Rest_ζ hE x z))) =
          hx (b3Rest_ζ hE x z) - C₀ := by
        simp only [C₀]
        linarith
      rw [this]
      ring
    · rw [mem_closedBall, dist_eq_norm, not_le] at hz
      show b3Rest_rho ε (z - p) * _ = b3Rest_rho ε (z - p) * _ - C₀ * b3Rest_rho ε (z - p)
      rw [b3Rest_rho_eq_zero hε hz.le]
      ring
  have hS : ∀ (r : ℂ) (H : ℂ → ℝ), ∫ z, b3Rest_rho ε (z - r) * H z =
      ∫ z, b3Rest_rho ε z * H (z + r) := by
    intro r H
    rw [← integral_add_right_eq_self (fun z ↦ b3Rest_rho ε (z - r) * H z) r]
    simp only [add_sub_cancel_right]
  have hf' : ∀ z, f z * hy (b3Rest_ζ hE y z) =
      dens z * hy (b3Rest_ζ hE y z) - b3Rest_rho ε (z - q) * hy (b3Rest_ζ hE y z) :=
    fun z ↦ sub_mul _ _ _
  simp only [hf']
  rw [integral_sub hi1 hi2, hD, hS q (fun z ↦ hy (b3Rest_ζ hE y z)),
    hS p (fun z ↦ hx (b3Rest_ζ hE x z))]
  ring

end HodgeLean.Foundations.Program
