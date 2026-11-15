import HodgeLean.Foundations.Program.CurveJacobianUnimodZeros

/-! # Track B3, lane Unimod: the real primitive mod `1` of a form with integral real periods

Let `θ` be a holomorphic form on a connected Riemann surface whose loop periods have integral real
parts. Fix a base point `p₀` and a good path `γ_p` from `p₀` to each `p`, and put
`f p = Re ∫_{γ_p} θ` (`b3Unimod_f`). Then
* `f q - f p ≡ Re ∫_η θ (mod 1)` for every good path `η` from `p` to `q`
  (`b3Unimod_f_good`): `γ_p · η · γ_q⁻¹` is a closed good path, hence a loop;
* the same holds along every `C¹` path on every interval `[a, b]` (`b3Unimod_f_path`);
* the level sets `{f ∈ c + ℤ}` are closed (`b3Unimod_isClosed_level`): near each point `f` is,
  mod `1`, the real part of a primitive of the disc coefficient.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [ConnectedSpace C]

/-- **The real primitive of `θ` from `p₀`**, along the chosen good paths. -/
def b3Unimod_f (θ : b3_HolForm E C) (p₀ : C) (p : C) : ℝ :=
  (b3_pathIntegral E C (b3A_joined (E := E) p₀ p).choose θ.1).re

variable {θ : b3_HolForm E C} (hint : ∀ γ : b3_SmoothLoop E C, ∃ m : ℤ, (b3_period E C γ θ).re = m)
include hint

/-- `f q - f p ≡ Re ∫_η θ (mod 1)` along good paths. -/
theorem b3Unimod_f_good (p₀ : C) {η : ℝ → C} {p q : C} (hη : b3A_IsGoodPath (E := E) η p q) :
    ∃ m : ℤ, b3Unimod_f θ p₀ q - b3Unimod_f θ p₀ p =
      (b3_pathIntegral E C η θ.1).re + m := by
  set γp := (b3A_joined (E := E) p₀ p).choose
  set γq := (b3A_joined (E := E) p₀ q).choose
  have hp : b3A_IsGoodPath (E := E) γp p₀ p := (b3A_joined (E := E) p₀ p).choose_spec
  have hq : b3A_IsGoodPath (E := E) γq p₀ q := (b3A_joined (E := E) p₀ q).choose_spec
  have h1 := hp.trans hη
  have hτ := h1.trans hq.symm
  obtain ⟨m, hm⟩ := hint (b3A_toLoop hτ)
  change (b3_pathIntegral E C (b3A_toLoop hτ).1 θ.1).re = m at hm
  rw [b3A_toLoop_pathIntegral, b3A_pathIntegral_trans θ.2 h1 hq.symm,
    b3A_pathIntegral_trans θ.2 hp hη, b3A_pathIntegral_symm θ.2 _ hq.1] at hm
  refine ⟨-m, ?_⟩
  simp only [Complex.add_re, Complex.neg_re] at hm
  simp only [b3Unimod_f]
  push_cast
  linarith

/-- `f (γ b) - f (γ a) ≡ Re ∫_a^b θ (mod 1)` along `C¹` paths. -/
theorem b3Unimod_f_path (p₀ : C) {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (a b : ℝ) :
    ∃ m : ℤ, b3Unimod_f θ p₀ (γ b) - b3Unimod_f θ p₀ (γ a) =
      (∫ t in a..b, θ.1 ⟨γ t, b3_velocity E C γ t⟩).re + m := by
  set σ : ℝ → ℝ := fun s ↦ a + (b - a) * s
  have hσ : ContDiff ℝ 1 σ := contDiff_const.add (contDiff_const.mul contDiff_id)
  have hγσ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (γ ∘ σ) := hγ.comp hσ.contMDiff
  have hgood := b3A_isGoodPath_reparam (γ ∘ σ) hγσ
  have e0 : (γ ∘ σ) 0 = γ a := by simp [σ]
  have e1 : (γ ∘ σ) 1 = γ b := by simp [σ]
  rw [e0, e1] at hgood
  obtain ⟨m, hm⟩ := b3Unimod_f_good hint p₀ hgood
  refine ⟨m, ?_⟩
  rw [hm, b3A_pathIntegral_reparam θ.2 _ hγσ]
  have := b3A_integral_reparam θ.2 γ hγ σ hσ 0 1
  simp only [σ, mul_zero, add_zero, mul_one, add_sub_cancel] at this
  rw [b3_pathIntegral]
  exact congrArg (fun z : ℂ ↦ z.re + (m : ℝ)) this

/-- Near each point, `f` is mod `1` a continuous function. -/
theorem b3Unimod_f_local (hE : Module.finrank ℂ E = 1) (p₀ q : C) :
    ∃ h : C → ℝ, ContinuousAt h q ∧ h q = b3Unimod_f θ p₀ q ∧
      ∀ᶠ y in 𝓝 q, ∃ m : ℤ, b3Unimod_f θ p₀ y = h y + m := by
  set u := b3Rest_e hE
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u (b3Rest_e_ne_zero hE) q
  obtain ⟨G, hG⟩ : Complex.IsExactOn (b3A_discCoef θ.1 q u) (Metric.ball (0 : ℂ) R) :=
    DifferentiableOn.isExactOn_ball fun z hz ↦ (b3A_discCoef_differentiableAt θ.2 q u
      (hR z (mem_ball_zero_iff.1 hz))).differentiableWithinAt
  set h : C → ℝ := fun y ↦ b3Unimod_f θ p₀ q + (G (b3Unimod_ζ hE q y) - G 0).re
  have hsrc : (chartAt E q).source ∈ 𝓝 q :=
    (chartAt E q).open_source.mem_nhds (mem_chart_source E q)
  have hζc : ContinuousAt (b3Unimod_ζ hE q) q := (b3Unimod_continuousOn_ζ hE q).continuousAt hsrc
  have hGc : ContinuousAt G 0 :=
    (hG 0 (Metric.mem_ball_self hR0)).differentiableAt.continuousAt
  refine ⟨h, ?_, ?_, ?_⟩
  · refine continuousAt_const.add (Complex.continuous_re.continuousAt.comp ?_)
    refine ContinuousAt.sub ?_ continuousAt_const
    refine ContinuousAt.comp (g := G) ?_ hζc
    rw [b3Unimod_ζ_self]
    exact hGc
  · simp [h, b3Unimod_ζ_self]
  · have hball : ∀ᶠ y in 𝓝 q, b3Unimod_ζ hE q y ∈ Metric.ball (0 : ℂ) R := by
      have := hζc.tendsto
      rw [b3Unimod_ζ_self] at this
      exact this (Metric.ball_mem_nhds 0 hR0)
    filter_upwards [hball, hsrc] with y hy hys
    set z := b3Unimod_ζ hE q y
    have hz : ‖z‖ < R := mem_ball_zero_iff.1 hy
    have hs := b3A_isGoodPath_segment q (chartAt E q q) (chartAt E q q + z • u)
      (b3A_segment_subset u q hR z hz)
    rw [(chartAt E q).left_inv (mem_chart_source E q)] at hs
    have hdisc : (chartAt E q).symm (chartAt E q q + z • u) = y := b3Unimod_disc_ζ hE hys
    rw [hdisc] at hs
    obtain ⟨m, hm⟩ := b3Unimod_f_good hint p₀ hs
    have hint' := b3A_segment_integral θ.2 (b3Unimod_κ hE) u (b3Unimod_κ_spec hE)
      (b3Unimod_κ_e hE) q hR hG z hz
    rw [hint'] at hm
    exact ⟨m, by simp only [h]; linarith⟩

/-- **The level sets `{f ∈ c + ℤ}` are closed.** -/
theorem b3Unimod_isClosed_level (hE : Module.finrank ℂ E = 1) (p₀ : C) (c : ℝ) :
    IsClosed {y : C | ∃ m : ℤ, b3Unimod_f θ p₀ y = c + m} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro q hq
  obtain ⟨h, hc, hq', hev⟩ := b3Unimod_f_local hint hE p₀ q
  set d := h q - c
  have hd : ∀ k : ℤ, d ≠ k := fun k hk ↦ hq ⟨k, by rw [← hq']; simp only [d] at hk; linarith⟩
  have h1 : (⌊d⌋ : ℝ) < d := lt_of_le_of_ne (Int.floor_le d) fun e ↦ hd _ e.symm
  have h2 : d < ⌊d⌋ + 1 := Int.lt_floor_add_one d
  have hcd : ContinuousAt (fun y ↦ h y - c) q := hc.sub continuousAt_const
  filter_upwards [hev, hcd.eventually (lt_mem_nhds h1), hcd.eventually (gt_mem_nhds h2)]
    with y ⟨m, hm⟩ hy1 hy2
  rintro ⟨k, hk⟩
  have : h y - c = (k - m : ℤ) := by push_cast; linarith
  rw [this] at hy1 hy2
  have a : ⌊d⌋ < k - m := by exact_mod_cast hy1
  have b : k - m < ⌊d⌋ + 1 := by exact_mod_cast hy2
  omega

end HodgeLean.Foundations.Program
