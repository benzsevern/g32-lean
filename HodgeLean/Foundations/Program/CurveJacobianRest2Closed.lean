import HodgeLean.Foundations.Program.CurveJacobianRestHodge

/-! # Track B3, lane Rest2: dual forms of loops are closed

* `b3Rest2_eq_zero_of_integral_smulFun`: a smooth `2`-form `μ` on a compact Riemann surface with
  `∫ g μ = 0` for every smooth function `g` vanishes. If `μ(z₀) ≠ 0`, take `g = ψ f` in the chart at
  `z₀`, with `f` the density of `μ` in that chart and `ψ` a bump at `z₀`: in every chart `g μ` has
  density `ψ f² det > 0` (the atlas is oriented), so `∫ g μ > 0`.
* `b3Rest2_d_eq_zero_of_dual`: a smooth `1`-form `η` with `∫ ω ∧ η = ∫_P ω` for all closed `ω`
  is closed: `∫ g dη = ∫ d(g η) - ∫ dg ∧ η = 0 - ∫_P dg = 0`.
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

/-- A smooth function supported in an open set, times a function smooth on that set, is smooth. -/
theorem b3Rest2_contDiff_mul_of_tsupport {f g : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hg : ContDiff ℝ ∞ g) (hgU : tsupport g ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun u ↦ g u * f u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ U
  · exact hg.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hu))
  · have : u ∉ tsupport g := fun h ↦ hu (hgU h)
    refine contDiffAt_const (c := (0 : ℝ)) |>.congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds this] with v hv
    simp [image_eq_zero_of_notMem_tsupport hv]

open scoped Classical in
/-- The function on `C` given by `φ` in the chart at `x`, extended by `0`. -/
def b3Rest2_efun (x : C) (φ : E → ℝ) : C → ℝ := fun p ↦
  if p ∈ (chartAt E x).source then φ (chartAt E x p) else 0

theorem b3Rest2_fun_efun (x : C) (φ : E → ℝ) :
    b3Forms_fun (E := E) (b3Rest2_efun x φ) =
      b3Rest_ofLoc x (fun u ↦ constOfIsEmpty ℝ E (Fin 0) (φ u)) := by
  funext p
  by_cases hp : p ∈ (chartAt E x).source
  · simp only [b3Forms_fun, b3Rest2_efun, b3Rest_ofLoc, hp, ite_true]
    ext v
    simp
  · simp only [b3Forms_fun, b3Rest2_efun, b3Rest_ofLoc, hp, ite_false]
    ext v
    simp

/-- **Chart functions of compactly supported smooth functions are smooth.** -/
theorem b3Rest2_isSmooth_efun [T2Space C] (x : C) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ (chartAt E x).target) :
    b3Forms_IsSmooth (b3Forms_fun (E := E) (b3Rest2_efun x φ)) := by
  rw [b3Rest2_fun_efun]
  have h0 : constOfIsEmpty ℝ E (Fin 0) (0 : ℝ) = 0 := by ext v; simp
  refine b3Rest_isSmooth_ofLoc x ?_ (hφc.comp_left (g := constOfIsEmpty ℝ E (Fin 0)) h0)
    ((tsupport_comp_subset (g := constOfIsEmpty ℝ E (Fin 0)) h0 φ).trans hφs)
  exact (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).toContinuousLinearEquiv.contDiff.comp hφ

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

/-- **A smooth `2`-form whose products with all smooth functions integrate to `0` vanishes.** -/
theorem b3Rest2_eq_zero_of_integral_smulFun (hE : Module.finrank ℂ E = 1)
    {μ : C → E [⋀^Fin 2]→L[ℝ] ℝ} (hμ : b3Forms_IsSmooth μ)
    (h : ∀ g : C → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) g) →
      b3Forms_integral (b3Rest_b hE) (b3Forms_smulFun g μ) = 0) :
    μ = 0 := by
  set b := b3Rest_b hE
  by_contra hne
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, μ z₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  have hb : μ z₀ b ≠ 0 := by
    intro h0
    apply hz₀
    have := (μ z₀).toAlternatingMap.eq_smul_basis_det b
    ext v
    have hv := congrArg (fun A ↦ A v) this
    simp only [AlternatingMap.smul_apply, smul_eq_mul] at hv
    have hv' : (μ z₀) v = μ z₀ b * b.det v := hv
    rw [hv', h0, zero_mul]
    rfl
  set x := z₀
  set u₀ := chartAt E x x
  set f : E → ℝ := fun u ↦ b3Forms_loc μ x u b
  have hf : ContDiffOn ℝ ∞ f (chartAt E x).target := by
    have hev : ContDiff ℝ ∞ (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A b) :=
      (ContinuousAlternatingMap.apply ℝ E ℝ b).contDiff
    exact hev.comp_contDiffOn (hμ x)
  have hfu₀ : f u₀ = μ z₀ b := by
    show b3Forms_loc μ x (chartAt E x x) b = _
    rw [b3Forms_loc_self]
  have hu₀ : u₀ ∈ (chartAt E x).target := (chartAt E x).map_source (mem_chart_source E x)
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target u₀ hu₀
  let ψ : ContDiffBump u₀ := ⟨R / 4, R / 2, by positivity, by linarith⟩
  have hψs : tsupport ψ ⊆ (chartAt E x).target := by
    rw [ψ.tsupport_eq]
    exact (closedBall_subset_ball (by show R / 2 < R; linarith)).trans hRsub
  set φ : E → ℝ := fun u ↦ ψ u * f u
  have hφ : ContDiff ℝ ∞ φ :=
    b3Rest2_contDiff_mul_of_tsupport (chartAt E x).open_target ψ.contDiff hψs hf
  have hφc : HasCompactSupport φ := ψ.hasCompactSupport.mul_right
  have hφs : tsupport φ ⊆ (chartAt E x).target :=
    (tsupport_mul_subset_left).trans hψs
  set g := b3Rest2_efun x φ
  have hg := b3Rest2_isSmooth_efun x hφ hφc hφs
  have hor := b3Forms_oriented_complex (E := E) (C := C)
  -- the density of `g μ` in the chart at `y`
  have hdens : ∀ (y : C) (v : E), v ∈ (chartAt E y).target →
      (chartAt E y).symm v ∈ (chartAt E x).source →
      b3Forms_loc (b3Forms_smulFun g μ) y v b =
        ψ (b3Forms_tr y x v) * f (b3Forms_tr y x v) ^ 2 *
          LinearMap.det (fderiv ℝ (b3Forms_tr y x) v : E →ₗ[ℝ] E) := by
    intro y v hv hp
    have hvd : v ∈ b3Forms_trDom y x := ⟨hv, hp⟩
    rw [b3Forms_loc_smulFun]
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [b3Forms_loc_eq_comp μ hvd, b3Forms_comp_apply_basis]
    simp only [g, b3Rest2_efun, hp, ite_true, φ, f]
    have htr : chartAt E x ((chartAt E y).symm v) = b3Forms_tr y x v := rfl
    rw [htr]
    ring
  have hnn : ∀ (y : C) (v : E), v ∈ (chartAt E y).target →
      0 ≤ b3Forms_loc (b3Forms_smulFun g μ) y v b := by
    intro y v hv
    by_cases hp : (chartAt E y).symm v ∈ (chartAt E x).source
    · rw [hdens y v hv hp]
      exact mul_nonneg (mul_nonneg ψ.nonneg (sq_nonneg _)) (hor y x v ⟨hv, hp⟩).le
    · rw [b3Forms_loc_smulFun]
      simp [g, b3Rest2_efun, hp]
  have hpos : ∀ y : C, z₀ ∈ (chartAt E y).source →
      0 < b3Forms_loc (b3Forms_smulFun g μ) y (chartAt E y z₀) b := by
    intro y hy
    have hv := (chartAt E y).map_source hy
    have hp : (chartAt E y).symm (chartAt E y z₀) ∈ (chartAt E x).source := by
      rw [(chartAt E y).left_inv hy]; exact mem_chart_source E x
    rw [hdens y _ hv hp]
    have htr : b3Forms_tr y x (chartAt E y z₀) = u₀ := by
      show chartAt E x ((chartAt E y).symm (chartAt E y z₀)) = _
      rw [(chartAt E y).left_inv hy]
    rw [htr, ψ.one_of_mem_closedBall (mem_closedBall_self (by positivity)), one_mul, hfu₀]
    exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hb))) (hor y x _ ⟨hv, hp⟩)
  have := b3Forms_integral_pos b (b3Forms_IsSmooth.smulFun' hg hμ) hnn z₀ hpos
  rw [h g hg] at this
  exact lt_irrefl _ this

/-- **A form with `∫ dg ∧ η = 0` for all smooth `g` is closed.** -/
theorem b3Rest2_d_eq_zero_of_wedge_d (hE : Module.finrank ℂ E = 1)
    {η : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hη : b3Forms_IsSmooth η)
    (h : ∀ g : C → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) g) →
      b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g)) η) =
        0) :
    b3Forms_d η = 0 := by
  refine b3Rest2_eq_zero_of_integral_smulFun hE hη.d fun g hg ↦ ?_
  have hL := b3Forms_d_smulFun hg hη
  have hS := b3Forms_integral_d_eq_zero b3Forms_oriented_complex (b3Rest_b hE)
    (b3Forms_IsSmooth.smulFun' hg hη)
  rw [hL, b3Forms_integral_add (b3Rest_b hE) (hg.d.wedgeForm hη) (b3Forms_IsSmooth.smulFun' hg hη.d), h g hg,
    zero_add] at hS
  exact hS

/-- **Dual forms of loops are closed**: a smooth form `η` with `∫ ω ∧ η = ∫_P ω` for every
closed form `ω`, for a `C¹` loop `P`, is closed. -/
theorem b3Rest2_d_eq_zero_of_dual (hE : Module.finrank ℂ E = 1) {P : ℝ → C}
    (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P) (hper : Function.Periodic P 1)
    {η : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hη : b3Forms_IsSmooth η)
    (hη' : ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
      b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) = b3Forms_lineIntegral α P 0 1) :
    b3Forms_d η = 0 := by
  refine b3Rest2_d_eq_zero_of_wedge_d hE hη fun g hg ↦ ?_
  rw [hη' _ hg.d (b3Forms_d_d hg), b3Forms_lineIntegral_d hg hP]
  have : P 1 = P 0 := by simpa using hper 0
  rw [this, sub_self]

end HodgeLean.Foundations.Program
