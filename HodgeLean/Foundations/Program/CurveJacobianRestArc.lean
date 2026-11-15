import HodgeLean.Foundations.Program.CurveJacobianRestJunction

/-! # Track B3, lane Rest: smeared arcs

In the chart at `x`, with complex coordinate `z`, a `C¹` arc `c : [a, b] → ℂ` gives the vector
field `X(z) = ∫_a^b ρ_ε(z - c(t)) c'(t) dt` and the `1`-form `ι X`. For a closed form `ω` with
primitive `h` on a chart region containing the `ε`-neighbourhood of the arc,
`∫_C ω ∧ ι X = ∫ ρ_ε(w) (h(c(b) + w) - h(c(a) + w)) dw` (`b3Rest_integral_wedge_arcForm`):
Fubini, a translation and the fundamental theorem of calculus along the translated arcs.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

/-! ## The profile of a smeared arc -/

section Profile

/-- **The profile of a smeared arc**, `z ↦ ∫_a^b ρ_ε(z - c(t)) c'(t) dt`. -/
def b3Rest_arcK (ε : ℝ) (c c' : ℝ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ t in a..b, (b3Rest_rho ε (z - c t) : ℂ) * c' t

theorem b3Rest_arcK_contDiff (ε : ℝ) {c c' : ℝ → ℂ} (hc : Continuous c) (hc' : Continuous c')
    (a b : ℝ) : ContDiff ℝ ∞ (b3Rest_arcK ε c c' a b) := by
  have hF : ContDiff ℝ ∞ (fun q : ℂ × (ℂ × ℂ) ↦ (b3Rest_rho ε (q.1 - q.2.1) : ℂ) * q.2.2) :=
    (Complex.ofRealCLM.contDiff.comp ((b3Rest_rho_contDiff ε).comp
      (contDiff_fst.sub contDiff_snd.fst))).mul contDiff_snd.snd
  exact b3Rest_contDiff_intervalIntegral_comp (E' := ℂ) hF (hc.prodMk hc') a b

theorem b3Rest_arcK_eq_zero {ε : ℝ} (hε : 0 < ε) {c c' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) {z : ℂ}
    (hz : z ∉ thickening ε (c '' Icc a b)) : b3Rest_arcK ε c c' a b z = 0 := by
  unfold b3Rest_arcK
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ ?_
  rw [b3Rest_rho_eq_zero hε, Complex.ofReal_zero, zero_mul]
  by_contra hlt
  apply hz
  rw [mem_thickening_iff]
  exact ⟨c t, ⟨t, Ioc_subset_Icc_self ht, rfl⟩, by rw [dist_eq_norm]; exact not_le.1 hlt⟩

theorem b3Rest_tsupport_arcK {ε : ℝ} (hε : 0 < ε) {c c' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    tsupport (b3Rest_arcK ε c c' a b) ⊆ cthickening ε (c '' Icc a b) := by
  refine closure_minimal (fun z hz ↦ ?_) isClosed_cthickening
  by_contra h
  exact hz (b3Rest_arcK_eq_zero hε hab fun h' ↦ h (thickening_subset_cthickening _ _ h'))

theorem b3Rest_isCompact_cthickening_arc (ε : ℝ) {c : ℝ → ℂ} (hc : Continuous c) (a b : ℝ) :
    IsCompact (cthickening ε (c '' Icc a b)) :=
  (isCompact_Icc.image hc).cthickening

/-- Integrability on `[a, b] × ℂ` of a function continuous on a compact box and vanishing off it. -/
theorem b3Rest_integrable_prod {f : ℝ → ℂ → ℝ} {a b : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hc : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ K))
    (h0 : ∀ t ∈ Icc a b, ∀ z ∉ K, f t z = 0) (hab : a ≤ b) :
    Integrable (Function.uncurry f) ((volume.restrict (uIoc a b)).prod volume) := by
  rw [← Measure.restrict_univ (μ := (volume : Measure ℂ)), Measure.prod_restrict,
    ← Measure.volume_eq_prod]
  refine IntegrableOn.of_forall_sdiff_eq_zero (hc.integrableOn_compact (isCompact_Icc.prod hK))
    ((measurableSet_uIoc).prod MeasurableSet.univ) fun q hq ↦ ?_
  obtain ⟨⟨hq1, -⟩, hq2⟩ := hq
  rw [uIoc_of_le hab] at hq1
  have ht : q.1 ∈ Icc a b := Ioc_subset_Icc_self hq1
  exact h0 q.1 ht q.2 fun hz ↦ hq2 ⟨ht, hz⟩

end Profile

/-! ## The smeared arc as a form -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

/-- The field of the smeared arc in the chart at `x`. -/
def b3Rest_arcField (hE : Module.finrank ℂ E = 1) (x : C) (ε : ℝ) (c c' : ℝ → ℂ) (a b : ℝ) :
    E → E [⋀^Fin 1]→L[ℝ] ℝ := fun u ↦
  b3Rest_iota hE (b3Rest_arcK ε c c' a b ((b3Rest_L hE).symm (u - chartAt E x x)))

/-- **The smeared arc** in the chart at `x`, a `1`-form on `C`. -/
def b3Rest_arcForm (hE : Module.finrank ℂ E = 1) (x : C) (ε : ℝ) (c c' : ℝ → ℂ) (a b : ℝ) :
    C → E [⋀^Fin 1]→L[ℝ] ℝ :=
  b3Rest_ofLoc x (b3Rest_arcField hE x ε c c' a b)

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest_arcField_props (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ} (hε : 0 < ε)
    {c c' : ℝ → ℂ} (hc : Continuous c) (hc' : Continuous c') {a b : ℝ} (hab : a ≤ b) :
    ContDiff ℝ ∞ (b3Rest_arcField hE x ε c c' a b) ∧
      HasCompactSupport (b3Rest_arcField hE x ε c c' a b) ∧
      tsupport (b3Rest_arcField hE x ε c c' a b) ⊆
        b3Rest_ζ hE x '' cthickening ε (c '' Icc a b) := by
  set ψ : E → ℂ := fun u ↦ (b3Rest_L hE).symm (u - chartAt E x x)
  have hψ : ContDiff ℝ ∞ ψ := (b3Rest_L hE).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hK := (b3Rest_isCompact_cthickening_arc ε hc a b).image (b3Rest_continuous_ζ hE x)
  have hts : tsupport (b3Rest_arcField hE x ε c c' a b) ⊆
      b3Rest_ζ hE x '' cthickening ε (c '' Icc a b) := by
    refine closure_minimal (fun u hu ↦ ?_) hK.isClosed
    refine ⟨ψ u, ?_, b3Rest_ζ_L_symm hE x u⟩
    by_contra hn
    apply hu
    show b3Rest_iota hE (b3Rest_arcK ε c c' a b (ψ u)) = 0
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hn (b3Rest_tsupport_arcK hε hab h), _root_.map_zero]
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts⟩
  exact (b3Rest_iota hE).contDiff.comp ((b3Rest_arcK_contDiff ε hc hc' a b).comp hψ)

theorem b3Rest_isSmooth_arcForm [T2Space C] (hE : Module.finrank ℂ E = 1) (x : C) {ε : ℝ}
    (hε : 0 < ε) {c c' : ℝ → ℂ} (hc : Continuous c) (hc' : Continuous c') {a b : ℝ}
    (hab : a ≤ b)
    (harc : ∀ z ∈ cthickening ε (c '' Icc a b), b3Rest_ζ hE x z ∈ (chartAt E x).target) :
    b3Forms_IsSmooth (b3Rest_arcForm hE x ε c c' a b) := by
  obtain ⟨h1, h2, h3⟩ := b3Rest_arcField_props hE x hε hc hc' hab
  exact b3Rest_isSmooth_ofLoc x h1 h2 (h3.trans (by rintro _ ⟨z, hz, rfl⟩; exact harc z hz))

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 400000 in
/-- **The pairing of a closed form with a smeared arc**: for a primitive `h` of `ω` on an open set
`U` of the chart image containing the `ε`-neighbourhood of the arc,
`∫ ω ∧ ι X = ∫ ρ_ε(w) h(c(b) + w) dw - ∫ ρ_ε(w) h(c(a) + w) dw`. -/
theorem b3Rest_integral_wedge_arcForm (hE : Module.finrank ℂ E = 1)
    {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (x : C) {U : Set E} (hUo : IsOpen U)
    (hU : U ⊆ (chartAt E x).target) {h : E → ℝ}
    (hh : ∀ u ∈ U, HasFDerivAt h (b3Forms_toCLM (b3Forms_loc α x u)) u) {ε : ℝ} (hε : 0 < ε)
    {c c' : ℝ → ℂ} (hc : Continuous c) (hc' : Continuous c') {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t)
    (harc : ∀ z ∈ cthickening ε (c '' Icc a b), b3Rest_ζ hE x z ∈ U) :
    b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α (b3Rest_arcForm hE x ε c c' a b)) =
      (∫ w, b3Rest_rho ε w * h (b3Rest_ζ hE x (w + c b))) -
        ∫ w, b3Rest_rho ε w * h (b3Rest_ζ hE x (w + c a)) := by
  set cc := chartAt E x x
  set S := cthickening ε (c '' Icc a b)
  have hSc : IsCompact S := b3Rest_isCompact_cthickening_arc ε hc a b
  obtain ⟨hA, hAc, hAs⟩ := b3Rest_arcField_props hE x hε hc hc' hab
  have hAt : tsupport (b3Rest_arcField hE x ε c c' a b) ⊆ (chartAt E x).target :=
    hAs.trans (by rintro _ ⟨z, hz, rfl⟩; exact hU (harc z hz))
  have hβ : b3Forms_IsSmooth (b3Rest_arcForm hE x ε c c' a b) := b3Rest_isSmooth_ofLoc x hA hAc hAt
  have hζc := b3Rest_continuous_ζ hE x
  have hsupp : tsupport (b3Forms_wedgeForm α (b3Rest_arcForm hE x ε c c' a b)) ⊆
      (chartAt E x).source := by
    refine (closure_mono fun p hp ↦ ?_).trans ((b3Rest_tsupport_ofLoc x hAc hAt).trans ?_)
    · by_contra h0
      apply hp
      have h0' : b3Rest_arcForm hE x ε c c' a b p = 0 := Function.notMem_support.1 h0
      simp only [b3Forms_wedgeForm, h0', b3Rest_wedge_zero_right]
    · rintro _ ⟨u, hu, rfl⟩
      exact (chartAt E x).map_target (hAt hu)
  rw [b3Forms_integral_eq_chartIntegral _ b3Forms_oriented_complex (hα.wedgeForm hβ) hsupp,
    b3Forms_chartIntegral, b3Rest_integral_addHaar_eq hE _ cc]
  set H : ℂ → ℝ := fun z ↦ h (b3Rest_ζ hE x z)
  set V : Set ℂ := b3Rest_ζ hE x ⁻¹' U
  have hVo : IsOpen V := hUo.preimage hζc
  have hSV : S ⊆ V := fun z hz ↦ harc z hz
  have hζd : ∀ z, HasFDerivAt (b3Rest_ζ hE x) ((b3Rest_L hE : ℂ →L[ℝ] E)) z := fun z ↦
    ((b3Rest_L hE : ℂ →L[ℝ] E).hasFDerivAt (x := z)).const_add cc
  set D : ℂ → ℂ →L[ℝ] ℝ := fun z ↦
    (b3Forms_toCLM (b3Forms_loc α x (b3Rest_ζ hE x z))).comp (b3Rest_L hE : ℂ →L[ℝ] E)
  have hHd : ∀ z ∈ V, HasFDerivAt H (D z) z := fun z hz ↦ (hh _ hz).comp z (hζd z)
  have hDc : ContinuousOn D V := by
    have hl : ContinuousOn (fun z ↦ b3Forms_loc α x (b3Rest_ζ hE x z)) V :=
      ((hα x).continuousOn).comp hζc.continuousOn fun z hz ↦ hU hz
    have ht : Continuous (fun A : E [⋀^Fin 1]→L[ℝ] ℝ ↦ b3Forms_toCLM A) :=
      (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm.continuous
    exact ((ContinuousLinearMap.compL ℝ ℂ E ℝ).flip (b3Rest_L hE : ℂ →L[ℝ] E)).continuous.comp_continuousOn
      (ht.comp_continuousOn hl)
  have hHc : ContinuousOn H V := fun z hz ↦ (hHd z hz).continuousAt.continuousWithinAt
  have hψζ : ∀ z, (b3Rest_L hE).symm (b3Rest_ζ hE x z - cc) = z := b3Rest_L_symm_ζ hE x
  -- the density
  have hint_eq : ∀ z, b3Forms_chartFun (b3Rest_b hE) x
      (b3Forms_wedgeForm α (b3Rest_arcForm hE x ε c c' a b)) (cc + z • b3Rest_e hE) =
        D z (b3Rest_arcK ε c c' a b z) := by
    intro z
    show b3Forms_chartFun (b3Rest_b hE) x _ (b3Rest_ζ hE x z) = _
    by_cases hz : z ∈ V
    · have ht : b3Rest_ζ hE x z ∈ (chartAt E x).target := hU hz
      rw [b3Forms_chartFun, indicator_of_mem ht, b3Forms_loc_wedgeForm]
      show b3Forms_wedge _ _ _ = _
      rw [b3Rest_arcForm, b3Rest_loc_ofLoc_self x _ ht, b3Rest_arcField, hψζ, b3Rest_wedge_iota]
      rfl
    · have h0 : b3Rest_arcK ε c c' a b z = 0 :=
        image_eq_zero_of_notMem_tsupport fun h' ↦ hz (hSV (b3Rest_tsupport_arcK hε hab h'))
      rw [h0, _root_.map_zero, b3Forms_chartFun]
      by_cases ht : b3Rest_ζ hE x z ∈ (chartAt E x).target
      · rw [indicator_of_mem ht, b3Forms_loc_wedgeForm]
        show b3Forms_wedge _ _ _ = _
        rw [b3Rest_arcForm, b3Rest_loc_ofLoc_self x _ ht, b3Rest_arcField, hψζ, h0, _root_.map_zero,
          b3Rest_wedge_zero_right]
        rfl
      · rw [indicator_of_notMem ht]
  simp only [hint_eq]
  -- the integrand on `[a, b] × ℂ`
  set Ψ : ℝ → ℂ → ℝ := fun t z ↦ b3Rest_rho ε (z - c t) * D z (c' t)
  have hρc : Continuous (b3Rest_rho ε) := (b3Rest_rho_contDiff ε).continuous
  have hρ0 : ∀ t ∈ Icc a b, ∀ z ∉ S, b3Rest_rho ε (z - c t) = 0 := by
    intro t ht z hz
    refine b3Rest_rho_eq_zero hε ?_
    by_contra hlt
    exact hz (thickening_subset_cthickening _ _ (mem_thickening_iff.2
      ⟨c t, ⟨t, ht, rfl⟩, by rw [dist_eq_norm]; exact not_le.1 hlt⟩))
  have hΨc : ContinuousOn (Function.uncurry Ψ) (Icc a b ×ˢ S) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (hρc.comp (continuous_snd.sub (hc.comp continuous_fst))).continuousOn
    · have h1 : ContinuousOn (fun q : ℝ × ℂ ↦ D q.2) (Icc a b ×ˢ S) :=
        hDc.comp continuous_snd.continuousOn fun q hq ↦ hSV hq.2
      exact h1.clm_apply (hc'.comp continuous_fst).continuousOn
  have hΨi : Integrable (Function.uncurry Ψ) ((volume.restrict (uIoc a b)).prod volume) :=
    b3Rest_integrable_prod hSc hΨc (fun t ht z hz ↦ by
      show b3Rest_rho ε (z - c t) * _ = 0
      rw [hρ0 t ht z hz, zero_mul]) hab
  -- the density as an integral along the arc
  have hDK : ∀ z, D z (b3Rest_arcK ε c c' a b z) = ∫ t in a..b, Ψ t z := by
    intro z
    have hi : IntervalIntegrable (fun t ↦ (b3Rest_rho ε (z - c t) : ℂ) * c' t) volume a b :=
      ((Complex.continuous_ofReal.comp (hρc.comp (continuous_const.sub hc))).mul
        hc').intervalIntegrable _ _
    rw [b3Rest_arcK, ← (D z).intervalIntegral_comp_comm hi]
    congr 1
    funext t
    rw [show (b3Rest_rho ε (z - c t) : ℂ) * c' t = b3Rest_rho ε (z - c t) • c' t by
      rw [Complex.real_smul], map_smul, smul_eq_mul]
  simp only [hDK]
  rw [← intervalIntegral_integral_swap hΨi]
  -- translate each slice and swap back
  set Ψ' : ℝ → ℂ → ℝ := fun t w ↦ b3Rest_rho ε w * D (w + c t) (c' t)
  have hslice : ∀ t, ∫ z, Ψ t z = ∫ w, Ψ' t w := by
    intro t
    rw [← integral_add_right_eq_self (fun z ↦ Ψ t z) (c t)]
    simp only [Ψ, Ψ', add_sub_cancel_right]
  simp only [hslice]
  have hB : ∀ t ∈ Icc a b, ∀ w ∈ closedBall (0 : ℂ) ε, w + c t ∈ S := by
    intro t ht w hw
    refine mem_cthickening_of_dist_le _ (c t) _ _ ⟨t, ht, rfl⟩ ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    simpa using hw
  have hΨ'c : ContinuousOn (Function.uncurry Ψ') (Icc a b ×ˢ closedBall (0 : ℂ) ε) := by
    refine ContinuousOn.mul (hρc.comp continuous_snd).continuousOn ?_
    have h1 : ContinuousOn (fun q : ℝ × ℂ ↦ D (q.2 + c q.1)) (Icc a b ×ˢ closedBall (0 : ℂ) ε) :=
      hDc.comp (continuous_snd.add (hc.comp continuous_fst)).continuousOn
        fun q hq ↦ hSV (hB q.1 hq.1 q.2 hq.2)
    exact h1.clm_apply (hc'.comp continuous_fst).continuousOn
  have hΨ'i : Integrable (Function.uncurry Ψ') ((volume.restrict (uIoc a b)).prod volume) :=
    b3Rest_integrable_prod (isCompact_closedBall 0 ε) hΨ'c (fun t _ w hw ↦ by
      show b3Rest_rho ε w * _ = 0
      rw [b3Rest_rho_eq_zero hε, zero_mul]
      rw [mem_closedBall, dist_zero_right, not_le] at hw
      exact hw.le) hab
  rw [intervalIntegral_integral_swap hΨ'i]
  -- the fundamental theorem of calculus along the translated arcs
  have hint : ∀ w, b3Rest_rho ε w * H (w + c b) - b3Rest_rho ε w * H (w + c a) =
      ∫ t in a..b, Ψ' t w := by
    intro w
    by_cases hw : w ∈ closedBall (0 : ℂ) ε
    · rw [← mul_sub]
      simp only [Ψ']
      rw [intervalIntegral.integral_const_mul]
      congr 1
      refine (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := fun t ↦ H (w + c t))
        (f' := fun t ↦ D (w + c t) (c' t)) hab ?_ ?_ ?_).symm
      · exact hHc.comp (continuous_const.add hc).continuousOn fun t ht ↦ hSV (hB t ht w hw)
      · intro t ht
        exact ((hHd _ (hSV (hB t (Ioo_subset_Icc_self ht) w hw))).comp_hasDerivAt t
          ((hd t ht).const_add w)).hasDerivWithinAt
      · exact (ContinuousOn.clm_apply (hDc.comp (continuous_const.add hc).continuousOn
          fun t ht ↦ hSV (hB t ht w hw)) hc'.continuousOn).intervalIntegrable_of_Icc hab
    · rw [mem_closedBall, dist_zero_right, not_le] at hw
      simp only [Ψ', b3Rest_rho_eq_zero hε hw.le, zero_mul, sub_zero,
        intervalIntegral.integral_zero]
  simp only [← hint]
  have hi1 : ∀ p : ℂ, p ∈ c '' Icc a b → Integrable (fun w ↦ b3Rest_rho ε w * H (w + p)) := by
    rintro _ ⟨t, ht, rfl⟩
    refine b3Rest_integrable_mul_of_tsupport hρc ?_ ?_
      (hHc.comp (continuous_id.add continuous_const).continuousOn fun w hw ↦ hSV (hB t ht w hw))
    · exact (isCompact_closedBall (0 : ℂ) ε).of_isClosed_subset (isClosed_tsupport _)
        (by simpa using b3Rest_tsupport_rho_sub hε 0)
    · simpa using b3Rest_tsupport_rho_sub hε 0
  rw [integral_sub (hi1 _ ⟨b, right_mem_Icc.2 hab, rfl⟩) (hi1 _ ⟨a, left_mem_Icc.2 hab, rfl⟩)]

end HodgeLean.Foundations.Program
