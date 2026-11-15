import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Track B3, lane Rest: Weyl's lemma for the Cauchy–Riemann operator

**Weyl's lemma** (`b3Rest_weyl`): a function `u` integrable on a disc `B(c, R)` of `ℂ` with
`∫ u ∂̄ψ = 0` for every smooth `ψ` compactly supported in the disc agrees almost everywhere on
`B(c, R/2)` with a holomorphic function. Here `∂̄ψ = ψ_x + i ψ_y` (twice the usual operator).

The proof mollifies `u` with the radial bumps `ρ_ε(z) = e(1 - |z/ε|²)` (`e = expNegInvGlue`):
* `ρ_ε ⋆ u` is smooth, and its `∂̄` is `-∫ u ∂̄(ρ_ε(z - ·)) = 0`, so it is holomorphic on
  `B(c, R - ε)`;
* a holomorphic function equals its own `ρ_δ`-average up to the factor `∫ ρ_δ` (the mean value
  property on circles, in polar coordinates);
* `ρ_δ ⋆ (ρ_ε ⋆ u) = ρ_ε ⋆ (ρ_δ ⋆ u)` (Fubini), so `(ρ_δ ⋆ u) / ∫ρ_δ` does not depend on `δ`
  on `B(c, R/2)`;
* `(ρ_δ ⋆ u)/∫ρ_δ → u` almost everywhere (Lebesgue's differentiation theorem).
HC no distance; AV milestone no distance.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff Convolution

namespace HodgeLean.Foundations.Program

/-- The operator `∂̄ψ = ψ_x + i ψ_y` (twice the Cauchy–Riemann operator). -/
def b3Rest_dbar (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ ψ z 1 + Complex.I * fderiv ℝ ψ z Complex.I

/-- The radial bump `z ↦ e(1 - |z|²)`, positive exactly on the unit disc. -/
def b3Rest_bump (z : ℂ) : ℝ := expNegInvGlue (1 - ‖z‖ ^ 2)

/-- The mollifier `ρ_ε(z) = e(1 - |z/ε|²)`, as a complex-valued function. -/
def b3Rest_mol (ε : ℝ) (z : ℂ) : ℂ := (b3Rest_bump (ε⁻¹ • z) : ℂ)

theorem b3Rest_bump_contDiff : ContDiff ℝ ∞ b3Rest_bump :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem b3Rest_mol_contDiff (ε : ℝ) : ContDiff ℝ ∞ (b3Rest_mol ε) :=
  Complex.ofRealCLM.contDiff.comp (b3Rest_bump_contDiff.comp (contDiff_const_smul _))

theorem b3Rest_bump_nonneg (z : ℂ) : 0 ≤ b3Rest_bump z := expNegInvGlue.nonneg _

theorem b3Rest_bump_le_one (z : ℂ) : b3Rest_bump z ≤ 1 := by
  unfold b3Rest_bump expNegInvGlue
  split_ifs with h
  · norm_num
  · rw [Real.exp_le_one_iff, neg_nonpos]
    exact (inv_pos.2 (not_le.1 h)).le

theorem b3Rest_bump_eq_zero {z : ℂ} (hz : 1 ≤ ‖z‖) : b3Rest_bump z = 0 :=
  expNegInvGlue.zero_of_nonpos (by nlinarith [norm_nonneg z])

theorem b3Rest_bump_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < b3Rest_bump z :=
  expNegInvGlue.pos_of_pos (by nlinarith [norm_nonneg z])

theorem b3Rest_mol_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ε ≤ ‖z‖) : b3Rest_mol ε z = 0 := by
  rw [b3Rest_mol, b3Rest_bump_eq_zero, Complex.ofReal_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, inv_mul_eq_div, le_div_iff₀ hε,
    one_mul]
  exact hz

theorem b3Rest_tsupport_mol {ε : ℝ} (hε : 0 < ε) : tsupport (b3Rest_mol ε) ⊆ closedBall 0 ε := by
  refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (b3Rest_mol_eq_zero hε (not_le.1 h).le)

theorem b3Rest_hasCompactSupport_mol {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (b3Rest_mol ε) :=
  (isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _) (b3Rest_tsupport_mol hε)

theorem b3Rest_norm_mol_le (ε : ℝ) (z : ℂ) : ‖b3Rest_mol ε z‖ ≤ 1 := by
  rw [b3Rest_mol, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (b3Rest_bump_nonneg _)]
  exact b3Rest_bump_le_one _

theorem b3Rest_integrable_mol {ε : ℝ} (hε : 0 < ε) : Integrable (b3Rest_mol ε) :=
  (b3Rest_mol_contDiff ε).continuous.integrable_of_hasCompactSupport
    (b3Rest_hasCompactSupport_mol hε)

/-- The mass `∫ ρ_ε = ε² ∫ ρ₁`. -/
theorem b3Rest_integral_mol {ε : ℝ} (hε : 0 < ε) :
    ∫ z, b3Rest_mol ε z = (ε ^ 2 : ℝ) • ∫ z, b3Rest_mol 1 z := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ) (b3Rest_mol 1) hε.le
  rw [Complex.finrank_real_complex] at h
  simp only [b3Rest_mol, inv_one, one_smul] at h ⊢
  exact h

theorem b3Rest_integral_mol_one_pos : 0 < (∫ z, b3Rest_mol 1 z).re := by
  have hint := b3Rest_integrable_mol (one_pos (α := ℝ))
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  have hcont : Continuous fun z ↦ (b3Rest_mol 1 z).re :=
    Complex.continuous_re.comp (b3Rest_mol_contDiff 1).continuous
  have hnn : ∀ z, 0 ≤ (b3Rest_mol 1 z).re := fun z ↦ by
    simp only [b3Rest_mol, Complex.ofReal_re]; exact b3Rest_bump_nonneg _
  rw [integral_pos_iff_support_of_nonneg hnn hint.re]
  refine lt_of_lt_of_le ((isOpen_lt continuous_const hcont).measure_pos volume ⟨0, ?_⟩)
    (measure_mono fun z hz ↦ ne_of_gt hz)
  simp only [b3Rest_mol, inv_one, one_smul, Complex.ofReal_re, mem_ofPred_eq]
  exact b3Rest_bump_pos (by simp)

/-! ## The mollification is holomorphic -/

/-- The mollification `ρ_ε ⋆ g`, `x ↦ ∫ ρ_ε(t) g(x - t) dt`. -/
def b3Rest_moll (ε : ℝ) (g : ℂ → ℂ) : ℂ → ℂ :=
  b3Rest_mol ε ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g

theorem b3Rest_moll_apply (ε : ℝ) (g : ℂ → ℂ) (x : ℂ) :
    b3Rest_moll ε g x = ∫ t, b3Rest_mol ε t * g (x - t) := rfl

theorem b3Rest_hasFDerivAt_moll {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : Integrable g) (x : ℂ) :
    HasFDerivAt (b3Rest_moll ε g)
      ((fderiv ℝ (b3Rest_mol ε) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompL ℂ, volume] g) x) x :=
  (b3Rest_hasCompactSupport_mol hε).hasFDerivAt_convolution_left _
    ((b3Rest_mol_contDiff ε).of_le (by norm_num)) hg.locallyIntegrable x

theorem b3Rest_fderiv_moll_apply {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : Integrable g)
    (x v : ℂ) :
    (fderiv ℝ (b3Rest_mol ε) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompL ℂ, volume] g) x v =
      ∫ t, fderiv ℝ (b3Rest_mol ε) t v * g (x - t) := by
  have hc : Continuous (fderiv ℝ (b3Rest_mol ε)) :=
    (b3Rest_mol_contDiff ε).continuous_fderiv (by norm_num)
  have hex := ((b3Rest_hasCompactSupport_mol hε).fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℂ).precompL ℂ) hc hg.locallyIntegrable x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  rfl

/-- The `∂̄` of `t ↦ ψ(x - t)` is minus the `∂̄` of `ψ` at `x - t`. -/
theorem b3Rest_dbar_comp_sub {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x w : ℂ) :
    b3Rest_dbar (fun t ↦ ψ (x - t)) w = -b3Rest_dbar ψ (x - w) := by
  have h : HasFDerivAt (fun t ↦ ψ (x - t)) ((fderiv ℝ ψ (x - w)).comp
      (-ContinuousLinearMap.id ℝ ℂ)) w := by
    have h1 : HasFDerivAt (fun t : ℂ ↦ x - t) (-ContinuousLinearMap.id ℝ ℂ) w :=
      (hasFDerivAt_id w).const_sub x
    exact (hψ (x - w)).hasFDerivAt.comp w h1
  simp only [b3Rest_dbar, h.fderiv, ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.id_apply, map_neg]
  ring

theorem b3Rest_fderiv_eq_zero_of_notMem {ψ : ℂ → ℂ} {w : ℂ} (hw : w ∉ tsupport ψ) :
    fderiv ℝ ψ w = 0 := by
  have : ψ =ᶠ[𝓝 w] fun _ ↦ 0 := notMem_tsupport_iff_eventuallyEq.1 hw
  rw [this.fderiv_eq]
  simp

/-- **The mollification of a weakly holomorphic function is holomorphic** away from the
boundary. -/
theorem b3Rest_moll_differentiableAt {c : ℂ} {R ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ}
    (hg : Integrable g)
    (h : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball c R →
      ∫ w, g w * b3Rest_dbar ψ w = 0)
    {x : ℂ} (hx : closedBall x ε ⊆ ball c R) :
    DifferentiableAt ℂ (b3Rest_moll ε g) x := by
  set D := (fderiv ℝ (b3Rest_mol ε) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompL ℂ, volume] g) x
  have hD := b3Rest_hasFDerivAt_moll hε hg x
  have hfd : Differentiable ℝ (b3Rest_mol ε) :=
    (b3Rest_mol_contDiff ε).differentiable (by norm_num)
  -- the test function `ψ(w) = ρ_ε(x - w)`
  set ψ : ℂ → ℂ := fun w ↦ b3Rest_mol ε (x - w)
  have hψs : tsupport ψ ⊆ closedBall x ε := by
    refine closure_minimal (fun w hw ↦ ?_) isClosed_closedBall
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    by_contra hlt
    exact hw (b3Rest_mol_eq_zero hε (not_le.1 hlt).le)
  have hψ : ContDiff ℝ ∞ ψ := (b3Rest_mol_contDiff ε).comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall x ε).of_isClosed_subset (isClosed_tsupport _) hψs
  have h0 := h ψ hψ hψc (hψs.trans hx)
  have hc : Continuous (fderiv ℝ (b3Rest_mol ε)) :=
    (b3Rest_mol_contDiff ε).continuous_fderiv (by norm_num)
  have hint : ∀ v : ℂ, Integrable (fun t ↦ fderiv ℝ (b3Rest_mol ε) t v * g (x - t)) := by
    intro v
    have hcv : HasCompactSupport (fun t ↦ fderiv ℝ (b3Rest_mol ε) t v) :=
      ((b3Rest_hasCompactSupport_mol hε).fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ ↦ L v)
        (by simp)
    exact hcv.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
      (hc.clm_apply continuous_const) hg.locallyIntegrable x
  have hsum : D 1 + Complex.I * D Complex.I = 0 := by
    rw [b3Rest_fderiv_moll_apply hε hg, b3Rest_fderiv_moll_apply hε hg,
      ← integral_const_mul, ← integral_add (hint 1) ((hint _).const_mul _)]
    have e1 : ∀ t, fderiv ℝ (b3Rest_mol ε) t 1 * g (x - t) +
        Complex.I * (fderiv ℝ (b3Rest_mol ε) t Complex.I * g (x - t)) =
          b3Rest_dbar (b3Rest_mol ε) t * g (x - t) := fun t ↦ by
      simp only [b3Rest_dbar]; ring
    simp only [e1]
    rw [← integral_sub_left_eq_self _ volume x]
    have e2 : ∀ w, b3Rest_dbar (b3Rest_mol ε) (x - w) * g (x - (x - w)) =
        -(g w * b3Rest_dbar ψ w) := fun w ↦ by
      rw [b3Rest_dbar_comp_sub hfd x w, sub_sub_cancel]; ring
    simp only [e2, integral_neg, h0, neg_zero]
  have hDI : D Complex.I = Complex.I * D 1 := by
    have : Complex.I * (Complex.I * D Complex.I) = Complex.I * (-D 1) := by
      rw [eq_neg_of_add_eq_zero_right hsum]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_neg] at this
    linear_combination -this
  let D' : ℂ →L[ℂ] ℂ := D 1 • ContinuousLinearMap.id ℂ ℂ
  have hDD : D'.restrictScalars ℝ = D := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv : v = (v.re : ℂ) + v.im * Complex.I := (Complex.re_add_im v).symm
    simp only [D', ContinuousLinearMap.coe_restrictScalars', _root_.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    conv_rhs => rw [hv]
    rw [map_add, show (v.re : ℂ) = (v.re : ℝ) • (1 : ℂ) by simp,
      show (v.im : ℂ) * Complex.I = (v.im : ℝ) • Complex.I by simp, map_smul, map_smul, hDI]
    simp only [Complex.real_smul]
    conv_lhs => rw [hv]
    ring
  exact (hasFDerivAt_of_restrictScalars ℝ hD hDD).differentiableAt

/-! ## The mean value property against the mollifier -/

/-- The radial profile of the mollifier. -/
def b3Rest_prof (δ r : ℝ) : ℂ := (expNegInvGlue (1 - (δ⁻¹ * r) ^ 2) : ℂ)

theorem b3Rest_mol_polar {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    b3Rest_mol δ (Complex.polarCoord.symm (r, θ)) = b3Rest_prof δ r := by
  simp only [b3Rest_mol, b3Rest_bump, b3Rest_prof, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hδ, Complex.norm_polarCoord_symm, abs_of_pos hr]

theorem b3Rest_prof_eq_zero {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : δ ≤ r) : b3Rest_prof δ r = 0 := by
  rw [b3Rest_prof, expNegInvGlue.zero_of_nonpos, Complex.ofReal_zero]
  have : 1 ≤ δ⁻¹ * r := by rw [inv_mul_eq_div, le_div_iff₀ hδ, one_mul]; exact hr
  nlinarith

theorem b3Rest_continuous_polarCoord_symm : Continuous fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

/-- **Integration against the mollifier in polar coordinates**: if the circle integrals of `G`
around `x` are `2π G x` for radii below `δ`, then `∫ ρ_δ(t) G(x - t) dt` is a fixed multiple of
`G x`. -/
theorem b3Rest_integral_mol_mul {δ : ℝ} (hδ : 0 < δ) (x : ℂ) {G : ℂ → ℂ}
    (hFc : Continuous fun t ↦ b3Rest_mol δ t * G (x - t))
    (hcirc : ∀ r ∈ Ioo (0 : ℝ) δ,
      ∫ θ in Ioo (-π) π, G (x - Complex.polarCoord.symm (r, θ)) = 2 * π * G x) :
    ∫ t, b3Rest_mol δ t * G (x - t) =
      (∫ r in Ioi (0 : ℝ), r • (b3Rest_prof δ r * (2 * π))) * G x := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  set f : ℝ × ℝ → ℂ := fun p ↦ p.1 • (b3Rest_mol δ (Complex.polarCoord.symm p) *
    G (x - Complex.polarCoord.symm p))
  have hfc : Continuous f :=
    continuous_fst.smul (hFc.comp b3Rest_continuous_polarCoord_symm)
  have hint : IntegrableOn f (Ioi 0 ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have h1 : IntegrableOn f (Icc 0 δ ×ˢ Icc (-π) π) (volume.prod volume) :=
      hfc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine h1.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    have hrδ : δ < r := by
      by_contra hle
      exact hn ⟨⟨(mem_Ioi.1 hr).le, not_lt.1 hle⟩, hθ.1.le, hθ.2.le⟩
    simp only [f, b3Rest_mol_polar hδ (mem_Ioi.1 hr), b3Rest_prof_eq_zero hδ hrδ.le, zero_mul,
      smul_zero]
  rw [← Measure.volume_eq_prod] at hint
  rw [Measure.volume_eq_prod, setIntegral_prod f (by rwa [← Measure.volume_eq_prod])]
  have hin : ∀ r ∈ Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, f (r, θ) =
      r • (b3Rest_prof δ r * (2 * π)) * G x := by
    intro r hr
    simp only [f, b3Rest_mol_polar hδ (mem_Ioi.1 hr)]
    rw [integral_smul, integral_const_mul]
    by_cases hrδ : r < δ
    · rw [hcirc r ⟨hr, hrδ⟩, smul_mul_assoc]
      ring_nf
    · simp [b3Rest_prof_eq_zero hδ (not_lt.1 hrδ)]
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_mul_const]

/-- **The mean value property on circles**, in polar coordinates. -/
theorem b3Rest_circle_mean {G : ℂ → ℂ} {x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hG : DifferentiableOn ℂ G (ball x R)) :
    ∫ θ in Ioo (-π) π, G (x - Complex.polarCoord.symm (r, θ)) = 2 * π * G x := by
  have e : ∀ θ : ℝ, x - Complex.polarCoord.symm (r, θ) = circleMap x r (θ + π) := by
    intro θ
    simp only [Complex.polarCoord_symm_apply, circleMap, Complex.ofReal_cos, Complex.ofReal_sin]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_mul_I]
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_add_right (fun φ ↦ G (circleMap x r φ)) π,
    show -π + π = 0 by ring, show π + π = 2 * π by ring]
  have hd : DiffContOnCl ℂ G (ball x |r|) := by
    rw [abs_of_pos hr]; exact hG.diffContOnCl_ball (closedBall_subset_ball hrR)
  have hmv := hd.circleAverage
  have hmv' := hmv
  rw [Real.circleAverage_def] at hmv'
  have h2 : (2 * π : ℝ) ≠ 0 := by positivity
  have := congrArg (fun z : ℂ ↦ ((2 * π : ℝ) : ℂ) * z) hmv'
  simp only [Complex.real_smul] at this
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h2, Complex.ofReal_one, one_mul] at this
  rw [this]
  push_cast
  ring

theorem b3Rest_continuous_mol_mul {δ R : ℝ} (hδR : δ < R) (hδ : 0 < δ) {x : ℂ} {G : ℂ → ℂ}
    (hG : ContinuousOn G (ball x R)) : Continuous fun t ↦ b3Rest_mol δ t * G (x - t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : ‖t‖ < R
  · have hx : x - t ∈ ball x R := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact ht
    have hGc : ContinuousAt G (x - t) := hG.continuousAt (isOpen_ball.mem_nhds hx)
    exact ((b3Rest_mol_contDiff δ).continuous.continuousAt).mul
      (hGc.comp (continuousAt_const.sub continuousAt_id))
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    have hU : {s : ℂ | δ < ‖s‖} ∈ 𝓝 t :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds (by
        show δ < ‖t‖; linarith [not_lt.1 ht])
    filter_upwards [hU] with s hs
    rw [b3Rest_mol_eq_zero hδ (le_of_lt hs), zero_mul]

/-- **A holomorphic function equals its mollified average up to the mass of the mollifier.** -/
theorem b3Rest_mol_mean {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {x : ℂ} {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball x R)) :
    ∫ t, b3Rest_mol δ t * G (x - t) = (∫ t, b3Rest_mol δ t) * G x := by
  have h1 := b3Rest_integral_mol_mul hδ x (G := G)
    (b3Rest_continuous_mol_mul hδR hδ hG.continuousOn)
    (fun r hr ↦ b3Rest_circle_mean hr.1 (hr.2.trans hδR) hG)
  have h2 := b3Rest_integral_mol_mul hδ x (G := fun _ ↦ (1 : ℂ))
    (b3Rest_continuous_mol_mul hδR hδ (x := x) (G := fun _ ↦ (1 : ℂ)) continuousOn_const)
    (fun r _ ↦ by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      simp only [Complex.real_smul, mul_one]
      push_cast
      ring)
  simp only [mul_one] at h2
  rw [h1, h2]

/-! ## Mollifications converge almost everywhere -/

theorem b3Rest_integral_mol_ne_zero {δ : ℝ} (hδ : 0 < δ) : ∫ t, b3Rest_mol δ t ≠ 0 := by
  rw [b3Rest_integral_mol hδ]
  have h1 : ∫ z, b3Rest_mol 1 z ≠ 0 := fun h ↦ by
    have := b3Rest_integral_mol_one_pos; rw [h] at this; simp at this
  exact smul_ne_zero (by positivity) h1

/-- **Lebesgue's differentiation theorem for the mollifier**: `(ρ_δ ⋆ g)(x) / ∫ ρ_δ → g x` for
almost every `x`. -/
theorem b3Rest_ae_tendsto_moll {g : ℂ → ℂ} (hg : Integrable g) :
    ∀ᵐ x, Tendsto (fun δ ↦ (∫ t, b3Rest_mol δ t)⁻¹ * b3Rest_moll δ g x) (𝓝[>] 0) (𝓝 (g x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hg.locallyIntegrable 1]
    with x hx
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have hlim := hx (fun _ ↦ x) id tendsto_id (hpos.mono fun δ hδ ↦ by
    simp only [id, one_mul, mem_closedBall, dist_self]; exact hδ.le)
  have hm₁ : ∫ z, b3Rest_mol 1 z ≠ 0 := fun h ↦ by
    have := b3Rest_integral_mol_one_pos; rw [h] at this; simp at this
  set m₁ := ∫ z, b3Rest_mol 1 z
  set V₁ := (volume : Measure ℂ).real (ball 0 1)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (by simpa using hlim.const_mul (V₁ / ‖m₁‖))
  filter_upwards [hpos] with δ hδ
  set A := ⨍ y in closedBall x δ, ‖g y - g x‖
  have hmδ : ∫ t, b3Rest_mol δ t = (δ ^ 2 : ℝ) • m₁ := b3Rest_integral_mol hδ
  have hmδ0 := b3Rest_integral_mol_ne_zero hδ
  have hint1 : Integrable (fun t ↦ b3Rest_mol δ t * g (x - t)) :=
    (b3Rest_hasCompactSupport_mol hδ).convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
      (b3Rest_mol_contDiff δ).continuous hg.locallyIntegrable x
  have hint2 : Integrable (fun t ↦ b3Rest_mol δ t * g x) := (b3Rest_integrable_mol hδ).mul_const _
  have hdiff : (∫ t, b3Rest_mol δ t)⁻¹ * b3Rest_moll δ g x - g x =
      (∫ t, b3Rest_mol δ t)⁻¹ * ∫ t, b3Rest_mol δ t * (g (x - t) - g x) := by
    rw [b3Rest_moll_apply]
    simp only [mul_sub]
    rw [integral_sub hint1 hint2, integral_mul_const, mul_sub, ← mul_assoc, inv_mul_cancel₀ hmδ0,
      one_mul]
  -- the integral of `‖g - g x‖` over the closed ball
  have hgx : IntegrableOn (fun y ↦ ‖g y - g x‖) (closedBall x δ) :=
    (hg.integrableOn.sub ((continuous_const (y := g x)).continuousOn.integrableOn_compact
      (isCompact_closedBall x δ))).norm
  have hind : Integrable ((closedBall x δ).indicator fun y ↦ ‖g y - g x‖) :=
    hgx.integrable_indicator measurableSet_closedBall
  have key : ‖∫ t, b3Rest_mol δ t * (g (x - t) - g x)‖ ≤ ∫ y in closedBall x δ, ‖g y - g x‖ := by
    calc ‖∫ t, b3Rest_mol δ t * (g (x - t) - g x)‖
        ≤ ∫ t, ‖b3Rest_mol δ t * (g (x - t) - g x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (closedBall x δ).indicator (fun y ↦ ‖g y - g x‖) (x - t) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t ↦ norm_nonneg _)
          (hind.comp_sub_left x) (Eventually.of_forall fun t ↦ ?_)
        show ‖b3Rest_mol δ t * (g (x - t) - g x)‖ ≤
          (closedBall x δ).indicator (fun y ↦ ‖g y - g x‖) (x - t)
        by_cases ht : x - t ∈ closedBall x δ
        · rw [indicator_of_mem ht, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (b3Rest_norm_mol_le δ t)
        · rw [indicator_of_notMem ht]
          have : δ ≤ ‖t‖ := by
            rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] at ht
            exact (not_le.1 ht).le
          rw [b3Rest_mol_eq_zero hδ this, zero_mul, norm_zero]
      _ = ∫ y, (closedBall x δ).indicator (fun y ↦ ‖g y - g x‖) y :=
        integral_sub_left_eq_self _ volume x
      _ = ∫ y in closedBall x δ, ‖g y - g x‖ := integral_indicator measurableSet_closedBall
  have hvol : (volume : Measure ℂ).real (closedBall x δ) = δ ^ 2 * V₁ := by
    rw [Measure.addHaar_real_closedBall volume x hδ.le, Complex.finrank_real_complex]
  have hvol0 : (volume : Measure ℂ).real (closedBall x δ) ≠ 0 := by
    rw [hvol]
    have : 0 < V₁ := by
      simp only [V₁, measureReal_def]
      exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne'
        measure_ball_lt_top.ne
    positivity
  have hav : ∫ y in closedBall x δ, ‖g y - g x‖ = (volume : Measure ℂ).real (closedBall x δ) * A := by
    simp only [A, setAverage_eq, smul_eq_mul]
    field_simp
  rw [hdiff, norm_mul, norm_inv, hmδ, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (δ ^ 2 * ‖m₁‖)⁻¹ * ‖∫ t, b3Rest_mol δ t * (g (x - t) - g x)‖
      ≤ (δ ^ 2 * ‖m₁‖)⁻¹ * (δ ^ 2 * V₁ * A) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hvol, ← hav]
        exact key
    _ = V₁ / ‖m₁‖ * A := by
        have : ‖m₁‖ ≠ 0 := norm_ne_zero_iff.2 hm₁
        field_simp

/-! ## Mollifications commute -/

/-- **`ρ_δ ⋆ (ρ_ε ⋆ g) = ρ_ε ⋆ (ρ_δ ⋆ g)`**, by Fubini. -/
theorem b3Rest_moll_comm {ε δ : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : Integrable g)
    (x : ℂ) :
    ∫ s, b3Rest_mol δ s * b3Rest_moll ε g (x - s) =
      ∫ t, b3Rest_mol ε t * b3Rest_moll δ g (x - t) := by
  set H : ℂ → ℂ → ℂ := fun s t ↦ b3Rest_mol δ s * (b3Rest_mol ε t * g (x - s - t))
  have hK := (b3Rest_integrable_mol hε).convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hg
    (μ := volume) (ν := volume)
  have hmp : MeasurePreserving (fun p : ℂ × ℂ ↦ (x - p.1, p.2)) (volume.prod volume)
      (volume.prod volume) :=
    (Measure.measurePreserving_sub_left volume x).prod (MeasurePreserving.id volume)
  have hK' := hmp.integrable_comp_of_integrable hK
  have hH : Integrable (Function.uncurry H) (volume.prod volume) := by
    have := hK'.bdd_mul (c := 1) (f := fun p : ℂ × ℂ ↦ b3Rest_mol δ p.1)
      ((b3Rest_mol_contDiff δ).continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ b3Rest_norm_mol_le δ p.1)
    refine this.congr (Eventually.of_forall fun p ↦ ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.mul_apply', H, Function.uncurry, sub_sub]
  have e1 : ∀ s, b3Rest_mol δ s * b3Rest_moll ε g (x - s) = ∫ t, H s t := fun s ↦ by
    rw [b3Rest_moll_apply, ← integral_const_mul]
  have e2 : ∀ t, b3Rest_mol ε t * b3Rest_moll δ g (x - t) = ∫ s, H s t := fun t ↦ by
    rw [b3Rest_moll_apply, ← integral_const_mul]
    congr 1
    funext s
    simp only [H, sub_sub]
    rw [add_comm t s]
    ring
  simp only [e1, e2]
  exact integral_integral_swap hH

/-! ## Weyl's lemma -/

/-- **Weyl's lemma for `∂̄`**: an integrable function on a disc annihilating `∂̄` of all test
functions agrees almost everywhere on the half disc with a holomorphic function. -/
theorem b3Rest_weyl {c : ℂ} {R : ℝ} (hR : 0 < R) {u : ℂ → ℂ} (hu : IntegrableOn u (ball c R))
    (h : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball c R →
      ∫ w, u w * b3Rest_dbar ψ w = 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball c (R / 2)) ∧
      ∀ᵐ z, z ∈ ball c (R / 2) → u z = G z := by
  set g := (ball c R).indicator u
  have hg : Integrable g := hu.integrable_indicator measurableSet_ball
  have hg' : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball c R →
      ∫ w, g w * b3Rest_dbar ψ w = 0 := by
    intro ψ h1 h2 h3
    rw [← h ψ h1 h2 h3]
    congr 1
    funext w
    by_cases hw : w ∈ ball c R
    · simp [g, indicator_of_mem hw]
    · have : w ∉ tsupport ψ := fun h' ↦ hw (h3 h')
      simp [g, indicator_of_notMem hw, b3Rest_dbar, b3Rest_fderiv_eq_zero_of_notMem this]
  have hhol : ∀ δ, 0 < δ → δ < R / 8 →
      DifferentiableOn ℂ (b3Rest_moll δ g) (ball c (3 * R / 4)) := by
    intro δ hδ hδR y hy
    refine (b3Rest_moll_differentiableAt hδ hg hg' ?_).differentiableWithinAt
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball] at hy ⊢
    calc dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
      _ < R := by linarith
  set ε₀ := R / 16 with hε₀v
  have hε₀ : 0 < ε₀ := by positivity
  have hkey : ∀ δ, 0 < δ → δ < R / 8 → ∀ x ∈ ball c (R / 2),
      (∫ t, b3Rest_mol δ t)⁻¹ * b3Rest_moll δ g x =
        (∫ t, b3Rest_mol ε₀ t)⁻¹ * b3Rest_moll ε₀ g x := by
    intro δ hδ hδR x hx
    have hball : ∀ δ', 0 < δ' → δ' < R / 8 →
        DifferentiableOn ℂ (b3Rest_moll δ' g) (ball x (R / 4)) := by
      intro δ' h1 h2
      refine (hhol δ' h1 h2).mono fun y hy ↦ ?_
      rw [mem_ball] at hx hy ⊢
      calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
        _ < 3 * R / 4 := by linarith
    have h1 := b3Rest_mol_mean hδ (by linarith : δ < R / 4) (hball ε₀ hε₀ (by rw [hε₀v]; linarith))
    have h2 := b3Rest_mol_mean hε₀ (by rw [hε₀v]; linarith : ε₀ < R / 4) (hball δ hδ hδR)
    have h3 := b3Rest_moll_comm (δ := δ) hε₀ hg x
    rw [h1, h2] at h3
    have n1 := b3Rest_integral_mol_ne_zero hδ
    have n2 := b3Rest_integral_mol_ne_zero hε₀
    rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff n1 n2]
    linear_combination (-1 : ℂ) * h3
  refine ⟨fun z ↦ (∫ t, b3Rest_mol ε₀ t)⁻¹ * b3Rest_moll ε₀ g z, ?_, ?_⟩
  · exact ((hhol ε₀ hε₀ (by rw [hε₀v]; linarith)).mono (ball_subset_ball (by linarith))).const_mul _
  · filter_upwards [b3Rest_ae_tendsto_moll hg] with x hx hxb
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ t, b3Rest_mol δ t)⁻¹ * b3Rest_moll δ g x =
        (∫ t, b3Rest_mol ε₀ t)⁻¹ * b3Rest_moll ε₀ g x := by
      filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < R / 8)] with δ hδ
      exact hkey δ hδ.1 hδ.2 x hxb
    have hlim2 := (tendsto_const_nhds (x := (∫ t, b3Rest_mol ε₀ t)⁻¹ * b3Rest_moll ε₀ g x)
      (f := 𝓝[>] (0 : ℝ))).congr' (hev.mono fun _ h ↦ h.symm)
    have := tendsto_nhds_unique hx hlim2
    have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hxb
    rw [← this]
    simp [g, indicator_of_mem hxR]

end HodgeLean.Foundations.Program
