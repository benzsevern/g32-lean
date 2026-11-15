import HodgeLean.Foundations.Program.CurveJacobianUnimodPrim

/-! # Track B3, lane Unimod: flat charts of a holomorphic form

A **flat chart** of a holomorphic form `θ` (`b3Unimod_Flat`) is an open partial homeomorphism
`F : C → ℂ` with `dF = θ`: along every `C¹` path `γ` through its source, `(F ∘ γ)' = θ(γ, γ')`; its
inverse is holomorphic, and its source lies in the chart at a point `q` where the coefficient of
`θ` does not vanish.
* `b3Unimod_exists_flat`: away from the zeros of `θ` there is a flat chart, a local inverse of a
  primitive of the disc coefficient (inverse function theorem);
* `b3Unimod_Flat.sub_eq`: along a `C¹` path in the source, `F (γ b) - F (γ a) = ∫_a^b θ`;
* `b3Unimod_Flat.eventually_sub`: two flat charts differ by a constant near each common point;
* `b3Unimod_Flat.symm_eq_symm`: if `F₁⁻¹ w₁ = F₂⁻¹ w₂` and the discs of radius `R` at `w₁`, `w₂`
  lie in the targets, then `F₁⁻¹ (w₁ + v) = F₂⁻¹ (w₂ + v)` for `|v| < R`;
* `b3Unimod_Flat.f_symm`: the real primitive mod `1` of `CurveJacobianUnimodPrim.lean` is
  `Re F` up to a constant and an integer.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- **The integrand in a chart**, for a path that is `C¹` at one parameter. -/
theorem b3Unimod_integrand_chart {θ : TangentBundle 𝓘(ℂ, E) C → ℂ} (hθ : θ ∈ b3_HolForm E C)
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ w : E, w = κ w • u) (γ : ℝ → C) (x : C) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ t) (ht : γ t ∈ (chartAt E x).source) :
    θ ⟨γ t, b3_velocity E C γ t⟩ = κ (deriv (chartAt E x ∘ γ) t) * b3A_coef θ x u (γ t) := by
  rw [b3A_holForm_apply_eq hθ κ u hκ x ⟨γ t, b3_velocity E C γ t⟩ ht]
  congr 2
  rw [TangentBundle.trivializationAt_apply]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, fderivWithin_univ,
    CompTriple.comp_eq]
  rw [← (b3A_chart_comp γ t hγ x ht).2]
  rfl

variable (hE : Module.finrank ℂ E = 1)

/-- **A flat chart of `θ`**: a local coordinate `F` with `dF = θ`. -/
structure b3Unimod_Flat (θ : b3_HolForm E C) where
  /-- the coordinate -/
  F : OpenPartialHomeomorph C ℂ
  /-- the centre of the underlying chart -/
  q : C
  source_sub : F.source ⊆ (chartAt E q).source
  coef_ne : ∀ y ∈ F.source, b3A_coef θ.1 q (b3Rest_e hE) y ≠ 0
  smooth : ∀ w ∈ F.target, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω F.symm w
  hasDeriv : ∀ (γ : ℝ → C) (t : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ t → γ t ∈ F.source →
    HasDerivAt (fun s ↦ F (γ s)) (θ.1 ⟨γ t, b3_velocity E C γ t⟩) t

/-- The complex coordinate centred at `q`, as an open partial homeomorphism. -/
def b3Unimod_ζe (q : C) : OpenPartialHomeomorph C ℂ :=
  (chartAt E q).trans ((Homeomorph.subRight (chartAt E q q)).trans
    (b3Forms_lineEquiv hE (b3Rest_e_ne_zero hE)).symm.toHomeomorph).toOpenPartialHomeomorph

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Unimod_ζe_apply (q y : C) : b3Unimod_ζe hE q y = b3Unimod_ζ hE q y := rfl

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Unimod_ζe_source (q : C) : (b3Unimod_ζe hE q).source = (chartAt E q).source := by
  simp [b3Unimod_ζe]

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Unimod_ζe_symm_apply (q : C) (z : ℂ) :
    (b3Unimod_ζe hE q).symm z = b3A_disc q (b3Rest_e hE) z := by
  simp [b3Unimod_ζe, b3A_disc, b3Forms_lineEquiv_apply, add_comm]

variable {hE}

namespace b3Unimod_Flat

variable {θ : b3_HolForm E C} (Fl : b3Unimod_Flat hE θ)

/-- Real paths through the inverse of a flat chart are `C¹`. -/
theorem contMDiffAt_symm_comp {ℓ : ℝ → ℂ} {t : ℝ} (hℓ : ContDiffAt ℝ 1 ℓ t)
    (ht : ℓ t ∈ Fl.F.target) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun s ↦ Fl.F.symm (ℓ s)) t := by
  have h1 := Fl.smooth _ ht
  have h2 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 Fl.F.symm (ℓ t) := by
    have := b3A_contMDiffWithinAt_real (s := univ) (contMDiffWithinAt_univ.2 h1)
    exact (contMDiffWithinAt_univ.1 this).of_le le_top
  exact h2.comp t hℓ.contMDiffAt

/-- The primitive along a `C¹` path in the source. -/
theorem sub_eq {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) {a b : ℝ}
    (hab : ∀ s ∈ uIcc a b, γ s ∈ Fl.F.source) :
    Fl.F (γ b) - Fl.F (γ a) = ∫ s in a..b, θ.1 ⟨γ s, b3_velocity E C γ s⟩ := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs ↦ Fl.hasDeriv γ s (hγ s) (hab s hs))
    ((b3A_continuous_integrand γ hγ θ).intervalIntegrable a b)
  exact this.symm

/-- **Two flat charts differ by a constant near each common point.** -/
theorem eventually_sub (Fl' : b3Unimod_Flat hE θ) {y : C} (hy : y ∈ Fl.F.source)
    (hy' : y ∈ Fl'.F.source) :
    ∀ᶠ z in 𝓝 y, z ∈ Fl.F.source ∧ z ∈ Fl'.F.source ∧
      Fl'.F z - Fl.F z = Fl'.F y - Fl.F y := by
  set W := Fl.F.target ∩ Fl.F.symm ⁻¹' Fl'.F.source
  have hWo : IsOpen W := Fl.F.isOpen_inter_preimage_symm Fl'.F.open_source
  have hyW : Fl.F y ∈ W := ⟨Fl.F.map_source hy, by rw [mem_preimage, Fl.F.left_inv hy]; exact hy'⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hWo _ hyW
  have hN : Fl.F.source ∩ Fl.F ⁻¹' Metric.ball (Fl.F y) r ∈ 𝓝 y :=
    inter_mem (Fl.F.open_source.mem_nhds hy)
      ((Fl.F.continuousAt hy).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  filter_upwards [hN] with z ⟨hz, hzb⟩
  have hzW := hball hzb
  have hz' : z ∈ Fl'.F.source := by
    have := hzW.2
    rwa [mem_preimage, Fl.F.left_inv hz] at this
  refine ⟨hz, hz', ?_⟩
  -- the segment from `F y` to `F z` in the coordinates of `F`
  set w := Fl.F z - Fl.F y
  set ℓ : ℝ → ℂ := fun s ↦ Fl.F y + s * w
  have hℓc : ContDiff ℝ 1 ℓ := contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hI : ∀ s ∈ uIcc (0 : ℝ) 1, ℓ s ∈ W := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    refine hball ?_
    show dist (Fl.F y + s * w) (Fl.F y) < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    have : ‖w‖ < r := by rw [← dist_eq_norm]; exact hzb
    nlinarith [norm_nonneg w, hs.2]
  set γ : ℝ → C := fun s ↦ Fl.F.symm (ℓ s)
  have hk : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ Fl'.F (γ s) - Fl.F (γ s)) 0 s := by
    intro s hs
    have hsW := hI s hs
    have hγs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ s := Fl.contMDiffAt_symm_comp hℓc.contDiffAt hsW.1
    have := (Fl'.hasDeriv γ s hγs hsW.2).sub (Fl.hasDeriv γ s hγs (Fl.F.map_target hsW.1))
    rwa [sub_self] at this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hk intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at this
  have h0 : γ 0 = y := by simp [γ, ℓ, Fl.F.left_inv hy]
  have h1 : γ 1 = z := by simp [γ, ℓ, w, Fl.F.left_inv hz]
  simp only [h0, h1] at this
  linear_combination -this

/-- **Flat charts agree along discs**: if `F₁⁻¹ w₁ = F₂⁻¹ w₂` and the discs of radius `R` at
`w₁`, `w₂` lie in the targets, then `F₁⁻¹ (w₁ + v) = F₂⁻¹ (w₂ + v)` for `|v| < R`. -/
theorem symm_eq_symm [T2Space C] (Fl' : b3Unimod_Flat hE θ) {w w' : ℂ} {R : ℝ}
    (hR : Metric.ball w R ⊆ Fl.F.target) (hR' : Metric.ball w' R ⊆ Fl'.F.target)
    (h : Fl.F.symm w = Fl'.F.symm w') :
    ∀ v ∈ Metric.ball (0 : ℂ) R, Fl.F.symm (w + v) = Fl'.F.symm (w' + v) := by
  have hmem : ∀ (a : ℂ), ∀ v ∈ Metric.ball (0 : ℂ) R, a + v ∈ Metric.ball a R := by
    intro a v hv
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    rwa [mem_ball_zero_iff] at hv
  set A := {v : ℂ | v ∈ Metric.ball (0 : ℂ) R ∧ Fl.F.symm (w + v) = Fl'.F.symm (w' + v)}
  have hc1 : ∀ v ∈ Metric.ball (0 : ℂ) R, ContinuousAt (fun v ↦ Fl.F.symm (w + v)) v :=
    fun v hv ↦ (Fl.F.continuousAt_symm (hR (hmem w v hv))).comp (by fun_prop)
  have hc2 : ∀ v ∈ Metric.ball (0 : ℂ) R, ContinuousAt (fun v ↦ Fl'.F.symm (w' + v)) v :=
    fun v hv ↦ (Fl'.F.continuousAt_symm (hR' (hmem w' v hv))).comp (by fun_prop)
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro v ⟨hv, hvA⟩
    set z := Fl.F.symm (w + v)
    have hz : z ∈ Fl.F.source := Fl.F.map_target (hR (hmem w v hv))
    have hz' : z ∈ Fl'.F.source := hvA ▸ Fl'.F.map_target (hR' (hmem w' v hv))
    have hFz : Fl.F z = w + v := Fl.F.right_inv (hR (hmem w v hv))
    have hFz' : Fl'.F z = w' + v := by
      rw [hvA]; exact Fl'.F.right_inv (hR' (hmem w' v hv))
    have hev := (hc1 v hv).eventually (Fl.eventually_sub Fl' hz hz')
    filter_upwards [hev, Metric.isOpen_ball.mem_nhds hv] with v' ⟨h1, h2, h3⟩ hv'
    refine ⟨hv', ?_⟩
    have hF1 : Fl.F (Fl.F.symm (w + v')) = w + v' := Fl.F.right_inv (hR (hmem w v' hv'))
    rw [hF1, hFz, hFz'] at h3
    have : Fl'.F (Fl.F.symm (w + v')) = w' + v' := by linear_combination h3
    rw [← this, Fl'.F.left_inv h2]
  have hcl : closure A ∩ Metric.ball (0 : ℂ) R ⊆ A := by
    rintro v ⟨hvc, hv⟩
    refine ⟨hv, ?_⟩
    have hfr : ∃ᶠ v' in 𝓝 v, v' ∈ A := mem_closure_iff_frequently.1 hvc
    have ht := (hc1 v hv).tendsto.prodMk_nhds (hc2 v hv).tendsto
    have := isClosed_diagonal.mem_of_frequently_of_tendsto (hfr.mono fun v' hv' ↦ hv'.2) ht
    exact this
  intro v hv
  have hR0 : 0 < R := lt_of_le_of_lt dist_nonneg hv
  have h0A : (0 : ℂ) ∈ A := ⟨Metric.mem_ball_self hR0, by simpa using h⟩
  exact ((convex_ball (0 : ℂ) R).isPreconnected.subset_of_closure_inter_subset hAo
    ⟨0, Metric.mem_ball_self hR0, h0A⟩ hcl hv).2

/-- **The real primitive mod `1` in a flat chart**: `f (F⁻¹ w) - f y ≡ Re (w - F y) (mod 1)` along
a segment of the target. -/
theorem f_symm [ConnectedSpace C]
    (hint : ∀ γ : b3_SmoothLoop E C, ∃ m : ℤ, (b3_period E C γ θ).re = m) (p₀ : C) {y : C}
    (hy : y ∈ Fl.F.source) {w : ℂ} (hw : segment ℝ (Fl.F y) w ⊆ Fl.F.target) :
    ∃ m : ℤ, b3Unimod_f θ p₀ (Fl.F.symm w) - b3Unimod_f θ p₀ y = (w - Fl.F y).re + m := by
  set σ : ℝ → ℝ := b3A_step
  set ℓ : ℝ → ℂ := fun s ↦ Fl.F y + (σ s : ℂ) * (w - Fl.F y)
  have hσ : ContDiff ℝ 1 σ := b3A_step_contDiff
  have hℓc : ContDiff ℝ 1 ℓ :=
    contDiff_const.add ((Complex.ofRealCLM.contDiff.comp hσ).mul contDiff_const)
  have hℓ : ∀ s, ℓ s ∈ Fl.F.target := fun s ↦ by
    refine hw ?_
    rw [segment_eq_image']
    exact ⟨σ s, ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, by
      simp [ℓ, Complex.real_smul]⟩
  set γ : ℝ → C := fun s ↦ Fl.F.symm (ℓ s)
  have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ := fun s ↦
    Fl.contMDiffAt_symm_comp hℓc.contDiffAt (hℓ s)
  have hσ0 : σ 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hσ1 : σ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  have h0 : γ 0 = y := by simp [γ, ℓ, hσ0, Fl.F.left_inv hy]
  have h1 : γ 1 = Fl.F.symm w := by simp [γ, ℓ, hσ1]
  obtain ⟨m, hm⟩ := b3Unimod_f_path hint p₀ hγ 0 1
  have hsub := Fl.sub_eq hγ (a := 0) (b := 1) fun s _ ↦ Fl.F.map_target (hℓ s)
  rw [h0, h1, Fl.F.right_inv (hw (right_mem_segment ℝ _ _))] at hsub
  rw [h0, h1, ← hsub] at hm
  exact ⟨m, hm⟩

end b3Unimod_Flat

/-- **A flat chart away from the zeros of `θ`**: a local inverse of a primitive of the disc
coefficient, composed with the chart coordinate. -/
theorem b3Unimod_exists_flat (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) {p : C}
    (hp : p ∉ b3Unimod_Z θ) : ∃ Fl : b3Unimod_Flat hE θ, p ∈ Fl.F.source := by
  set u := b3Rest_e hE
  set κ := b3Unimod_κ hE
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u (b3Rest_e_ne_zero hE) p
  set g := b3A_discCoef θ.1 p u
  obtain ⟨G, hG⟩ : Complex.IsExactOn g (Metric.ball (0 : ℂ) R) :=
    DifferentiableOn.isExactOn_ball fun z hz ↦ (b3A_discCoef_differentiableAt θ.2 p u
      (hR z (mem_ball_zero_iff.1 hz))).differentiableWithinAt
  have hgc : ContinuousOn g (Metric.ball (0 : ℂ) R) := fun z hz ↦
    (b3A_discCoef_differentiableAt θ.2 p u (hR z (mem_ball_zero_iff.1 hz))).continuousAt
      |>.continuousWithinAt
  set O := Metric.ball (0 : ℂ) R ∩ g ⁻¹' {0}ᶜ
  have hOo : IsOpen O := hgc.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
  have hgζ : ∀ y ∈ (chartAt E p).source, g (b3Unimod_ζ hE p y) = b3A_coef θ.1 p u y := by
    intro y hy
    simp only [g, b3A_discCoef]
    rw [b3Unimod_disc_ζ hE hy]
  have hg0 : g 0 ≠ 0 := by
    have := hgζ p (mem_chart_source E p)
    rw [b3Unimod_ζ_self] at this
    rw [this]
    exact fun h ↦ hp ((b3Unimod_coef_eq_zero_iff hE θ (mem_chart_source E p)).1 h)
  have hGc : ContDiffOn ℂ ω G (Metric.ball (0 : ℂ) R) :=
    DifferentiableOn.contDiffOn (fun z hz ↦ (hG z hz).differentiableAt.differentiableWithinAt)
      Metric.isOpen_ball
  have hGc0 : ContDiffAt ℂ ω G 0 := hGc.contDiffAt (Metric.ball_mem_nhds 0 hR0)
  have hf' := (hG 0 (Metric.mem_ball_self hR0)).hasFDerivAt_equiv hg0
  set H := hGc0.toOpenPartialHomeomorph G hf' (by simp)
  have hHc : ⇑H = G := rfl
  set H' := H.restrOpen O hOo
  set Fz := b3Unimod_ζe hE p
  set F := Fz.trans H'
  have hFapply : ∀ y, F y = G (b3Unimod_ζ hE p y) := fun y ↦ rfl
  have hFsymm : ∀ w, F.symm w = b3A_disc p u (H.symm w) := fun w ↦ by
    show Fz.symm (H.symm w) = _
    rw [b3Unimod_ζe_symm_apply]
  have hFsrc : ∀ y ∈ F.source, y ∈ (chartAt E p).source ∧ b3Unimod_ζ hE p y ∈ H.source ∩ O := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    refine ⟨by rw [← b3Unimod_ζe_source hE p]; exact hy.1, ?_⟩
    have := hy.2
    rwa [mem_preimage, OpenPartialHomeomorph.restrOpen_source] at this
  refine ⟨⟨F, p, fun y hy ↦ (hFsrc y hy).1, fun y hy ↦ ?_, fun w hw ↦ ?_, fun γ t hγ ht ↦ ?_⟩, ?_⟩
  · obtain ⟨hys, -, hO⟩ := hFsrc y hy
    rw [← hgζ y hys]
    exact hO.2
  · -- the inverse is holomorphic
    have hw' : w ∈ H'.target := by
      have := hw
      rw [OpenPartialHomeomorph.trans_target] at this
      exact this.1
    have ha : H'.symm w ∈ H'.source := H'.map_target hw'
    rw [OpenPartialHomeomorph.restrOpen_source] at ha
    have hwH : w ∈ H.target := by
      have := hw'
      simp only [H', OpenPartialHomeomorph.restrOpen_toPartialEquiv] at this
      exact this.1
    set a := H.symm w
    have haR : a ∈ Metric.ball (0 : ℂ) R := ha.2.1
    have hga : g a ≠ 0 := ha.2.2
    have h1 : ContDiffAt ℂ ω H.symm w :=
      H.contDiffAt_symm hwH ((hG a haR).hasFDerivAt_equiv hga)
        (hGc.contDiffAt (Metric.isOpen_ball.mem_nhds haR))
    have h2 := (b3A_disc_contMDiffAt p u (hR a (mem_ball_zero_iff.1 haR))).comp w h1.contMDiffAt
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun w' ↦ ?_)
    exact hFsymm w'
  · -- the derivative along paths
    obtain ⟨hys, -, hO⟩ := hFsrc (γ t) ht
    have hc := b3A_chart_comp γ t hγ p hys
    have hd : HasDerivAt (chartAt E p ∘ γ) (deriv (chartAt E p ∘ γ) t) t :=
      (hc.1.differentiableAt one_ne_zero).hasDerivAt
    have hζ : HasDerivAt (fun s ↦ b3Unimod_ζ hE p (γ s)) (κ (deriv (chartAt E p ∘ γ) t)) t := by
      have := (κ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hd.sub_const (chartAt E p p))
      exact this
    have hGd := (hG _ hO.1).comp t hζ
    rw [b3Unimod_integrand_chart θ.2 κ u (b3Unimod_κ_spec hE) γ p t hγ hys, ← hgζ _ hys,
      mul_comm]
    exact hGd
  · show p ∈ (Fz.trans H').source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [b3Unimod_ζe_source]; exact mem_chart_source E p
    · rw [mem_preimage, OpenPartialHomeomorph.restrOpen_source]
      refine ⟨?_, ?_, ?_⟩
      · show b3Unimod_ζ hE p p ∈ H.source
        rw [b3Unimod_ζ_self]
        exact hGc0.mem_toOpenPartialHomeomorph_source hf' (by simp)
      · show b3Unimod_ζ hE p p ∈ Metric.ball (0 : ℂ) R
        rw [b3Unimod_ζ_self]; exact Metric.mem_ball_self hR0
      · show g (b3Unimod_ζ hE p p) ≠ 0
        rw [b3Unimod_ζ_self]; exact hg0

end HodgeLean.Foundations.Program
