module

public import HodgeLean.Foundations.Mathlib.FredholmAnalyticDefs

/-! # Joint analyticity of evaluation on bounded holomorphic functions -/

@[expose] public noncomputable section

open Set Filter Topology Module Metric
open scoped BoundedContinuousFunction

namespace HodgeLean.Foundations

/-- Extension by zero of a bounded holomorphic function. -/
def b63r_eval_ext {U : Set ℂ} (f : b63r_bddHol U) : ℂ → ℂ :=
  fun z ↦ open Classical in if h : z ∈ U then ((f : U →ᵇ ℂ) ⟨z, h⟩) else 0

lemma b63r_eval_ext_norm_le {U : Set ℂ} (f : b63r_bddHol U) (z : ℂ) :
    ‖b63r_eval_ext f z‖ ≤ ‖f‖ := by
  unfold b63r_eval_ext
  by_cases h : z ∈ U
  · rw [dite_eq_left h]; exact BoundedContinuousFunction.norm_coe_le_norm _ _
  · rw [dite_eq_right h, norm_zero]; exact norm_nonneg _

lemma b63r_eval_ext_diff {U : Set ℂ} (f : b63r_bddHol U) :
    DifferentiableOn ℂ (b63r_eval_ext f) U := by
  obtain ⟨g, hg, hfg⟩ := f.2
  refine hg.congr fun z hz ↦ ?_
  simp only [b63r_eval_ext, dite_eq_left hz]
  exact hfg ⟨z, hz⟩

lemma b63r_eval_ext_add {U : Set ℂ} (f₁ f₂ : b63r_bddHol U) (z : ℂ) :
    b63r_eval_ext (f₁ + f₂) z = b63r_eval_ext f₁ z + b63r_eval_ext f₂ z := by
  unfold b63r_eval_ext
  by_cases h : z ∈ U
  · simp only [dite_eq_left h]; rfl
  · simp only [dite_eq_right h, add_zero]

lemma b63r_eval_ext_smul {U : Set ℂ} (c : ℂ) (f : b63r_bddHol U) (z : ℂ) :
    b63r_eval_ext (c • f) z = c * b63r_eval_ext f z := by
  unfold b63r_eval_ext
  by_cases h : z ∈ U
  · simp only [dite_eq_left h]; rfl
  · simp only [dite_eq_right h, mul_zero]

lemma b63r_eval_sphere_bound {d : ℂ → ℂ} {z₀ : ℂ} {R C : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ d (closedBall z₀ R)) (hC : ∀ w ∈ sphere z₀ R, ‖d w‖ ≤ C) :
    ∀ z ∈ closedBall z₀ R, ‖d z‖ ≤ C := by
  intro z hz
  have h1 : DiffContOnCl ℂ d (ball z₀ R) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball z₀ hR.ne']
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball h1 ?_ ?_
  · rwa [frontier_ball z₀ hR.ne']
  · rwa [closure_ball z₀ hR.ne']

lemma b63r_eval_est {g : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall z₀ R)) (hM : ∀ z, ‖g z‖ ≤ M) :
    (∀ z ∈ closedBall z₀ R, ‖dslope g z₀ z‖ ≤ 2 * M / R) ∧
    (∀ z ∈ closedBall z₀ R, ‖dslope (dslope g z₀) z₀ z‖ ≤ 4 * M / R ^ 2) := by
  have hn : closedBall z₀ R ∈ 𝓝 z₀ := closedBall_mem_nhds z₀ hR
  have hd1 : DifferentiableOn ℂ (dslope g z₀) (closedBall z₀ R) :=
    (Complex.differentiableOn_dslope hn).2 hg
  have hd2 : DifferentiableOn ℂ (dslope (dslope g z₀) z₀) (closedBall z₀ R) :=
    (Complex.differentiableOn_dslope hn).2 hd1
  have key : ∀ (d : ℂ → ℂ) (C : ℝ) (w : ℂ), w ∈ sphere z₀ R → ‖d w - d z₀‖ ≤ C →
      ‖dslope d z₀ w‖ ≤ C / R := by
    intro d C w hw hC
    have hne : w ≠ z₀ := ne_of_mem_sphere hw hR.ne'
    rw [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv, mem_sphere_iff_norm.1 hw,
      inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hC hR.le
  have b1 : ∀ z ∈ closedBall z₀ R, ‖dslope g z₀ z‖ ≤ 2 * M / R := by
    refine b63r_eval_sphere_bound hR hd1 fun w hw ↦ key g _ w hw ?_
    calc ‖g w - g z₀‖ ≤ ‖g w‖ + ‖g z₀‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM w, hM z₀]
  refine ⟨b1, b63r_eval_sphere_bound hR hd2 fun w hw ↦ ?_⟩
  have := key (dslope g z₀) (4 * M / R) w hw ?_
  · rwa [div_div, ← sq] at this
  calc ‖dslope g z₀ w - dslope g z₀ z₀‖ ≤ ‖dslope g z₀ w‖ + ‖dslope g z₀ z₀‖ := norm_sub_le _ _
    _ ≤ 2 * M / R + 2 * M / R :=
        add_le_add (b1 w (sphere_subset_closedBall hw)) (b1 z₀ (mem_closedBall_self hR.le))
    _ = 4 * M / R := by ring

/-- Evaluation at `z` (zero off `U`) as a continuous linear functional. -/
def b63r_eval_G (U : Set ℂ) (z : ℂ) : b63r_bddHol U →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ b63r_eval_ext f z
      map_add' := fun f₁ f₂ ↦ b63r_eval_ext_add f₁ f₂ z
      map_smul' := fun c f ↦ b63r_eval_ext_smul c f z } 1
    fun f ↦ by
      change ‖b63r_eval_ext f z‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact b63r_eval_ext_norm_le f z

lemma b63r_eval_G_apply (U : Set ℂ) (z : ℂ) (f : b63r_bddHol U) :
    b63r_eval_G U z f = b63r_eval_ext f z := rfl

/-- The derivative functional at `z₀`. -/
def b63r_eval_L {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {R : ℝ}
    (hR : 0 < R) (hB : closedBall z₀ R ⊆ U) : b63r_bddHol U →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ deriv (b63r_eval_ext f) z₀
      map_add' := fun f₁ f₂ ↦ by
        have h₁ := (b63r_eval_ext_diff f₁).differentiableAt (hU.mem_nhds hz₀)
        have h₂ := (b63r_eval_ext_diff f₂).differentiableAt (hU.mem_nhds hz₀)
        have : b63r_eval_ext (f₁ + f₂) = fun z ↦ b63r_eval_ext f₁ z + b63r_eval_ext f₂ z :=
          funext (b63r_eval_ext_add f₁ f₂)
        simp only [this]
        exact deriv_add h₁ h₂
      map_smul' := fun c f ↦ by
        have : b63r_eval_ext (c • f) = fun z ↦ c * b63r_eval_ext f z :=
          funext (b63r_eval_ext_smul c f)
        simp only [this, deriv_const_mul_field', RingHom.id_apply, smul_eq_mul] } (2 / R)
    fun f ↦ by
      have := (b63r_eval_est hR ((b63r_eval_ext_diff f).mono hB)
        (b63r_eval_ext_norm_le f)).1 z₀ (mem_closedBall_self hR.le)
      rw [dslope_same] at this
      change ‖deriv (b63r_eval_ext f) z₀‖ ≤ 2 / R * ‖f‖
      exact this.trans_eq (by ring)

lemma b63r_eval_G_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {R : ℝ}
    (hR : 0 < R) (hB : closedBall z₀ R ⊆ U) :
    HasDerivAt (b63r_eval_G U) (b63r_eval_L hU hz₀ hR hB) z₀ := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_sub_sub z₀ one_lt_two)
  refine Asymptotics.IsBigO.of_bound (4 / R ^ 2) ?_
  filter_upwards [closedBall_mem_nhds z₀ hR] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦ ?_
  set g := b63r_eval_ext f
  obtain ⟨-, b2⟩ := b63r_eval_est hR ((b63r_eval_ext_diff f).mono hB) (b63r_eval_ext_norm_le f)
  have e1 := sub_smul_dslope g z₀ z
  have e2 := sub_smul_dslope (dslope g z₀) z₀ z
  rw [dslope_same] at e2
  have : (b63r_eval_G U z - b63r_eval_G U z₀ - (z - z₀) • b63r_eval_L hU hz₀ hR hB) f
      = (z - z₀) ^ 2 * dslope (dslope g z₀) z₀ z := by
    simp only [sub_apply, smul_apply, b63r_eval_G_apply]
    change g z - g z₀ - (z - z₀) • deriv g z₀ = _
    simp only [smul_eq_mul] at e1 e2 ⊢
    rw [← e1, sq, mul_assoc, e2]
    ring
  rw [this, norm_mul, norm_pow]
  calc ‖z - z₀‖ ^ 2 * ‖dslope (dslope g z₀) z₀ z‖ ≤ ‖z - z₀‖ ^ 2 * (4 * ‖f‖ / R ^ 2) :=
        mul_le_mul_of_nonneg_left (b2 z hz) (by positivity)
    _ = 4 / R ^ 2 * ‖z - z₀‖ ^ 2 * ‖f‖ := by ring

lemma b63r_eval_G_analytic {U : Set ℂ} (hU : IsOpen U) : AnalyticOnNhd ℂ (b63r_eval_G U) U := by
  rw [Complex.analyticOnNhd_iff_differentiableOn hU]
  intro z₀ hz₀
  obtain ⟨R, hR, hB⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz₀)
  exact (b63r_eval_G_hasDerivAt hU hz₀ hR hB).differentiableAt.differentiableWithinAt

open Classical in
theorem b63r_eval_core {k : ℕ} {U : Set ℂ} (hU : IsOpen U) (W : Set (Fin k → ℂ))
    (hW : IsOpen W) (e : (Fin k → ℂ) → b63r_bddHol U) (he : AnalyticOnNhd ℂ e W) :
    AnalyticOnNhd ℂ
      (fun p : (Fin k → ℂ) × ℂ ↦ if h : p.2 ∈ U then ((e p.1 : b63r_bddHol U) : U →ᵇ ℂ) ⟨p.2, h⟩
        else 0) (W ×ˢ U) := by
  have _ := hW
  intro p hp
  have hfun : (fun p : (Fin k → ℂ) × ℂ ↦ if h : p.2 ∈ U then
      ((e p.1 : b63r_bddHol U) : U →ᵇ ℂ) ⟨p.2, h⟩ else 0) =
      fun p ↦ ContinuousLinearMap.apply ℂ ℂ (e p.1) (b63r_eval_G U p.2) := by
    funext q
    simp only [ContinuousLinearMap.apply_apply, b63r_eval_G_apply, b63r_eval_ext]
  rw [hfun]
  have h1 : AnalyticAt ℂ (fun q : (Fin k → ℂ) × ℂ ↦ e q.1) p :=
    (he p.1 hp.1).comp analyticAt_fst
  have h2 : AnalyticAt ℂ (fun q : (Fin k → ℂ) × ℂ ↦ b63r_eval_G U q.2) p :=
    (b63r_eval_G_analytic hU p.2 hp.2).comp analyticAt_snd
  have h3 := (ContinuousLinearMap.apply ℂ ℂ :
    b63r_bddHol U →L[ℂ] (b63r_bddHol U →L[ℂ] ℂ) →L[ℂ] ℂ).analyticAt_bilinear
      (e p.1, b63r_eval_G U p.2)
  exact h3.comp₂ h1 h2

end HodgeLean.Foundations
