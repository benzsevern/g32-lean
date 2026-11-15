import HodgeLean.Foundations.Program.CurveJacobianAFiniteDim
import HodgeLean.Foundations.Program.CurveJacobianAPathInt

/-! # Track B3, lane A: forms with vanishing periods

In a chart, the integral of a holomorphic form along a segment from the centre is the difference of
the values of a primitive of its disc coefficient. On a compact connected surface, a form whose
loop periods all vanish has a well-defined integral from a base point, which is holomorphic, hence
constant; the form, its differential, is then zero.
-/

noncomputable section

open Manifold Filter Topology Set Bundle Metric
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Exact

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- **The integrand in a chart**: `θ(γ t, γ' t) = κ((φ ∘ γ)'(t)) · coef θ (γ t)`. -/
theorem b3A_integrand_chart {θ : TangentBundle 𝓘(ℂ, E) C → ℂ} (hθ : θ ∈ b3_HolForm E C)
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ w : E, w = κ w • u) (γ : ℝ → C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (x : C) (t : ℝ)
    (ht : γ t ∈ (chartAt E x).source) :
    b3A_integrand θ γ t = κ (deriv (chartAt E x ∘ γ) t) * b3A_coef θ x u (γ t) := by
  rw [b3A_integrand, b3A_holForm_apply_eq hθ κ u hκ x ⟨γ t, b3_velocity E C γ t⟩ ht]
  congr 2
  rw [TangentBundle.trivializationAt_apply]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, fderivWithin_univ,
    CompTriple.comp_eq]
  rw [← (b3A_chart_comp γ t (hγ t) x ht).2]
  rfl

omit [IsManifold 𝓘(ℂ, E) ω C] in
/-- Chart segments from the centre stay in the chart disc. -/
theorem b3A_segment_subset (u : E) (q : C) {R : ℝ}
    (hR : ∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target) (zp : ℂ)
    (hzp : ‖zp‖ < R) :
    segment ℝ (chartAt E q q) (chartAt E q q + zp • u) ⊆ (chartAt E q).target := by
  intro w hw
  rw [segment_eq_image'] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  have := hR ((s : ℂ) * zp) (by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖zp‖ ≤ 1 * ‖zp‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ < R := by rw [one_mul]; exact hzp)
  show chartAt E q q + s • (chartAt E q q + zp • u - chartAt E q q) ∈ _
  rw [add_sub_cancel_left, ← Complex.coe_smul, smul_smul]
  exact this

/-- **Integral along a chart segment from the centre**: with `G` a primitive of the disc
coefficient, the integral along `t ↦ φ⁻¹(φ q + σ(t) z u)` is `G z - G 0`. -/
theorem b3A_segment_integral {θ : TangentBundle 𝓘(ℂ, E) C → ℂ} (hθ : θ ∈ b3_HolForm E C)
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ w : E, w = κ w • u) (hκu : κ u = 1) (q : C) {R : ℝ}
    (hR : ∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target) {G : ℂ → ℂ}
    (hG : ∀ z ∈ ball (0 : ℂ) R, HasDerivAt G (b3A_discCoef θ q u z) z) (zp : ℂ)
    (hzp : ‖zp‖ < R) :
    b3_pathIntegral E C (fun t ↦ (chartAt E q).symm (chartAt E q q +
      Real.smoothTransition (3 * t - 1) • (chartAt E q q + zp • u - chartAt E q q))) θ =
      G zp - G 0 := by
  set c := chartAt E q q
  set σ : ℝ → ℝ := fun t ↦ Real.smoothTransition (3 * t - 1)
  have hσ : ContDiff ℝ 1 σ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hσd : Differentiable ℝ σ := hσ.differentiable one_ne_zero
  have hσ01 : ∀ t, 0 ≤ σ t ∧ σ t ≤ 1 := fun t ↦
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hsm : ∀ t, σ t • (c + zp • u - c) = ((σ t : ℂ) * zp) • u := by
    intro t
    rw [add_sub_cancel_left, ← Complex.coe_smul, smul_smul]
  have hnorm : ∀ t, ‖(σ t : ℂ) * zp‖ < R := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ01 t).1]
    calc σ t * ‖zp‖ ≤ 1 * ‖zp‖ := mul_le_mul_of_nonneg_right (hσ01 t).2 (norm_nonneg _)
      _ < R := by rw [one_mul]; exact hzp
  have hmem : ∀ t, c + σ t • (c + zp • u - c) ∈ (chartAt E q).target := fun t ↦ by
    rw [hsm]
    exact hR _ (hnorm t)
  have hseg := b3A_isGoodPath_segment q c (c + zp • u) (fun w hw ↦ by
    rw [segment_eq_image'] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have := hR ((s : ℂ) * zp) (by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖zp‖ ≤ 1 * ‖zp‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ < R := by rw [one_mul]; exact hzp)
    show c + s • (c + zp • u - c) ∈ _
    rw [add_sub_cancel_left, ← Complex.coe_smul, smul_smul]
    exact this)
  set seg : ℝ → C := fun t ↦ (chartAt E q).symm (c + σ t • (c + zp • u - c))
  have hchart : chartAt E q ∘ seg = fun t ↦ c + σ t • (c + zp • u - c) := by
    funext t
    exact (chartAt E q).right_inv (hmem t)
  have hint : ∀ t, b3A_integrand θ seg t =
      ((deriv σ t : ℝ) : ℂ) * zp * b3A_discCoef θ q u ((σ t : ℂ) * zp) := by
    intro t
    rw [b3A_integrand_chart hθ κ u hκ seg hseg.1 q t ((chartAt E q).map_target (hmem t)), hchart]
    have hd : deriv (fun t ↦ c + σ t • (c + zp • u - c)) t = deriv σ t • (c + zp • u - c) := by
      rw [deriv_const_add, deriv_smul_const (hσd t)]
    rw [hd, add_sub_cancel_left, ← Complex.coe_smul, map_smul, map_smul, hκu, smul_eq_mul,
      smul_eq_mul, mul_one]
    congr 1
    rw [b3A_discCoef, b3A_disc, ← hsm]
  have hderiv : ∀ t, HasDerivAt (fun t : ℝ ↦ G ((σ t : ℂ) * zp))
      (b3A_integrand θ seg t) t := by
    intro t
    rw [hint t]
    have h1 : HasDerivAt (fun t : ℝ ↦ (σ t : ℂ) * zp) (((deriv σ t : ℝ) : ℂ) * zp) t :=
      ((hσd t).hasDerivAt.ofReal_comp).mul_const zp
    have h2 := (hG _ (mem_ball_zero_iff.2 (hnorm t))).comp t h1
    rw [mul_comm] at h2
    exact h2
  have hcont := b3A_continuous_integrand seg hseg.1 ⟨θ, hθ⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable 0 1)
  have h0 : σ 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h1 : σ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  rw [h0, h1] at this
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul] at this
  exact this

omit [IsManifold 𝓘(ℂ, E) ω C] in
/-- A radius for the disc of a chart. -/
theorem b3A_chart_radius (u : E) (hu : u ≠ 0) (x : C) :
    ∃ R > 0, ∀ z : ℂ, ‖z‖ < R → chartAt E x x + z • u ∈ (chartAt E x).target := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target (chartAt E x x)
    ((chartAt E x).map_source (mem_chart_source E x))
  refine ⟨ε / ‖u‖, div_pos hε (norm_pos_iff.2 hu), fun z hz ↦ hball ?_⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
  rwa [lt_div_iff₀ (norm_pos_iff.2 hu)] at hz

/-- **A holomorphic form with vanishing periods on a compact connected surface is zero**: its
integral from a base point is a well-defined holomorphic function, hence constant, and the form is
its differential. -/
theorem b3A_eq_zero_of_periods [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (θ : b3_HolForm E C) (h : ∀ γ : b3_SmoothLoop E C, b3_period E C γ θ = 0) : θ = 0 := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  set b := Module.finBasisOfFinrankEq ℂ E hE
  set u := b 0
  set κ : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (b.coord 0)
  have hκ : ∀ w : E, w = κ w • u := by
    intro w
    conv_lhs => rw [← b.sum_repr w]
    simp [κ, u]
  have hκu : κ u = 1 := by simp [κ, u]
  have hu : u ≠ 0 := b.ne_zero 0
  obtain ⟨p₀⟩ : Nonempty C := inferInstance
  choose γp hγp using fun p : C ↦ b3A_joined (E := E) p₀ p
  set F : C → ℂ := fun p ↦ b3_pathIntegral E C (γp p) θ
  have hindep : ∀ (p : C) (δ : ℝ → C), b3A_IsGoodPath (E := E) δ p₀ p →
      b3_pathIntegral E C δ θ = F p := by
    intro p δ hδ
    have hτ := hδ.trans (hγp p).symm
    have h0 := h (b3A_toLoop hτ)
    change b3_pathIntegral E C (b3A_toLoop hτ).1 θ = 0 at h0
    rw [b3A_toLoop_pathIntegral, b3A_pathIntegral_trans θ.2 hδ (hγp p).symm,
      b3A_pathIntegral_symm θ.2 _ (hγp p).1] at h0
    exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h0)
  have hlocal : ∀ q : C, ∃ R > 0, ∃ G : ℂ → ℂ,
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt G (b3A_discCoef θ q u z) z) ∧
      (∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target) ∧
      ∀ z : ℂ, ‖z‖ < R → F (b3A_disc q u z) = F q + (G z - G 0) := by
    intro q
    obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u hu q
    obtain ⟨G, hG⟩ : Complex.IsExactOn (b3A_discCoef (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) q u)
        (ball (0 : ℂ) R) :=
      DifferentiableOn.isExactOn_ball fun z hz ↦ (b3A_discCoef_differentiableAt θ.2 q u
        (hR z (mem_ball_zero_iff.1 hz))).differentiableWithinAt
    refine ⟨R, hR0, G, hG, hR, fun z hz ↦ ?_⟩
    have hs := b3A_isGoodPath_segment q (chartAt E q q) (chartAt E q q + z • u)
      (b3A_segment_subset u q hR z hz)
    rw [(chartAt E q).left_inv (mem_chart_source E q)] at hs
    show F ((chartAt E q).symm (chartAt E q q + z • u)) = _
    rw [← hindep _ _ ((hγp q).trans hs), b3A_pathIntegral_trans θ.2 (hγp q) hs,
      b3A_segment_integral θ.2 κ u hκ hκu q hR hG z hz]
  have hdiffF : ∀ q, MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) F q := by
    intro q
    obtain ⟨R, hR0, G, hG, hR, hF⟩ := hlocal q
    set ζ : C → ℂ := fun y ↦ κ (chartAt E q y - chartAt E q q)
    have hζ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω ζ q := by
      have h1 := contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := q)
      have h2 : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun w : E ↦ κ (w - chartAt E q q)) :=
        (κ.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
      exact (h2 _).comp q h1
    have hζ0 : ζ q = 0 := by simp [ζ]
    have hev : ∀ᶠ y in 𝓝 q, F y = F q + (G (ζ y) - G 0) := by
      have hU : (chartAt E q).source ∩ {y | ‖ζ y‖ < R} ∈ 𝓝 q := by
        refine inter_mem ((chartAt E q).open_source.mem_nhds (mem_chart_source E q)) ?_
        exact hζ.continuousAt.preimage_mem_nhds (isOpen_lt continuous_norm continuous_const
          |>.mem_nhds (by simp [hζ0, hR0]))
      filter_upwards [hU] with y ⟨hy, hyR⟩
      have : b3A_disc q u (ζ y) = y := by
        rw [b3A_disc, ← hκ, add_sub_cancel]
        exact (chartAt E q).left_inv hy
      rw [← hF _ hyR, this]
    have hGd : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) G (ζ q) := by
      rw [hζ0]
      exact (hG 0 (mem_ball_self hR0)).differentiableAt.mdifferentiableAt
    refine MDifferentiableAt.congr_of_eventuallyEq ?_ hev
    exact mdifferentiableAt_const.add ((hGd.comp q (hζ.mdifferentiableAt (by simp))).sub
      mdifferentiableAt_const)
  have hconst : ∀ p, F p = F p₀ := fun p ↦
    (MDifferentiable.apply_eq_of_compactSpace (I := 𝓘(ℂ, E)) hdiffF p p₀)
  have hcoef : ∀ q, b3A_coef (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) q u q = 0 := by
    intro q
    obtain ⟨R, hR0, G, hG, hR, hF⟩ := hlocal q
    have hGc : ∀ᶠ z in 𝓝 (0 : ℂ), G z = G 0 := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hR0] with z hz
      have := hF z (mem_ball_zero_iff.1 hz)
      rw [hconst, hconst q] at this
      linear_combination -this
    have h1 := (hasDerivAt_const (0 : ℂ) (G 0)).congr_of_eventuallyEq hGc
    have h2 := (hG 0 (mem_ball_self hR0)).unique h1
    have : b3A_disc q u 0 = q := by
      rw [b3A_disc, zero_smul, add_zero]
      exact (chartAt E q).left_inv (mem_chart_source E q)
    rw [b3A_discCoef, this] at h2
    exact h2
  refine Subtype.ext (funext fun p ↦ ?_)
  rw [b3A_holForm_apply_eq θ.2 κ u hκ p.1 p (mem_chart_source E p.1), hcoef, mul_zero]
  rfl

end Exact

end HodgeLean.Foundations.Program
