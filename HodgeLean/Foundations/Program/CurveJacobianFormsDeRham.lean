import HodgeLean.Foundations.Program.CurveJacobianFormsTame

/-!
# Track B3 foundations (stage B3.4b): de Rham's theorem in degree one for loops

On a connected manifold, a smooth closed `1`-form whose periods along all `C¹` loops vanish is
exact (`b3Forms_exists_primitive`). Together with `b3Forms_lineIntegral_d` (exact forms have zero
periods) this says that the period map from `H¹_dR(M)` to functions on loops is injective
(`b3Forms_periodMap_injective`): closed forms modulo exact forms are detected by their periods.

The ingredients:
* the Poincaré lemma in a chart (`b3Forms_exists_local_primitive`), from Mathlib's
  `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`;
* line integrals through a local primitive (`b3Forms_lineIntegral_eq_of_primitive`);
* tame paths inside chart balls (`b3Forms_segPath`), which make every point of a connected
  manifold reachable by tame paths from a base point (`b3Forms_reachable`);
* the primitive `q ↦ ∫_{p₀}^{q} α`, well defined because the loop of `γ * δ⁻¹` has period
  `∫_γ α - ∫_δ α = 0`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Function
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

section Local

/-- A `1`-form `E → E [⋀^Fin 1]→L[ℝ] ℝ` read as a map `E → E →L[ℝ] ℝ`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_toCLM (A : E [⋀^Fin 1]→L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm A

theorem b3Forms_toCLM_apply (A : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    b3Forms_toCLM A v = A (fun _ ↦ v) := rfl

/-- **The Poincaré lemma in a chart**: a smooth closed `1`-form has a primitive on every open
convex subset of a chart image. -/
theorem b3Forms_exists_local_primitive {α : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hdα : b3Forms_d α = 0) (x : M) {U : Set E} (hUc : Convex ℝ U) (hUo : IsOpen U)
    (hU : U ⊆ (chartAt E x).target) :
    ∃ h : E → ℝ, ∀ w ∈ U, HasFDerivAt h (b3Forms_toCLM (b3Forms_loc α x w)) w := by
  set θ : E → E →L[ℝ] ℝ := fun w ↦ b3Forms_toCLM (b3Forms_loc α x w)
  have hdiff : ∀ w ∈ (chartAt E x).target, DifferentiableAt ℝ (b3Forms_loc α x) w :=
    fun w hw ↦ (hα.contDiffAt hw).differentiableAt (by simp)
  have hθd : ∀ w ∈ (chartAt E x).target, DifferentiableAt ℝ θ w := fun w hw ↦
    (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv
      |>.differentiableAt.comp w (hdiff w hw)
  refine hUc.exists_forall_hasFDerivAt_of_fderiv_symmetric hUo
    (fun w hw ↦ (hθd w (hU hw)).differentiableWithinAt) fun w hw a b ↦ ?_
  have hw := hU hw
  have h0 : extDeriv (b3Forms_loc α x) w = 0 := by
    rw [← b3Forms_loc_d hα x hw, hdα, b3Forms_loc_zero]
    rfl
  have h1 := congrArg (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![a, b]) h0
  simp only [extDeriv_apply (hdiff w hw), ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    at h1
  rw [Fin.sum_univ_two] at h1
  have e0 : Fin.removeNth 0 ![a, b] = fun _ ↦ b := by funext i; fin_cases i; rfl
  have e1 : Fin.removeNth 1 ![a, b] = fun _ ↦ a := by funext i; fin_cases i; rfl
  rw [e0, e1] at h1
  have hev : ∀ a' c : E,
      fderiv ℝ θ w a' c = fderiv ℝ (fun w' ↦ b3Forms_loc α x w' (fun _ ↦ c)) w a' :=
    fun a' c ↦ by
      rw [show (fun w' ↦ b3Forms_loc α x w' (fun _ ↦ c)) = fun w' ↦ θ w' c from rfl,
        fderiv_clm_apply (hθd w hw) (differentiableAt_const c)]
      simp
  rw [hev a b, hev b a]
  simp at h1
  linarith

/-- **Line integrals through a local primitive**: along a `C¹` path staying in the chart
domain of `x`, with chart image in a set where `h` is a primitive of the local representative,
`∫_γ α = h(γ b) - h(γ a)` in coordinates. -/
theorem b3Forms_lineIntegral_eq_of_primitive {α : M → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) {x : M} {U : Set E} {h : E → ℝ}
    (hh : ∀ w ∈ U, HasFDerivAt h (b3Forms_toCLM (b3Forms_loc α x w)) w) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) {a b : ℝ}
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ (chartAt E x).source ∧ chartAt E x (γ t) ∈ U) :
    b3Forms_lineIntegral α γ a b = h (chartAt E x (γ b)) - h (chartAt E x (γ a)) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := h ∘ (chartAt E x ∘ γ))
    (fun t ht ↦ ?_) (b3Forms_intervalIntegrable_lineIntegrand hα hγ a b)
  obtain ⟨hs, hU⟩ := hγU t ht
  have h1 := (hh _ hU).comp_hasDerivAt t (b3Forms_hasDerivAt_chart_comp hγ hs)
  rw [b3Forms_apply_velocity_eq_loc hγ α hs]
  exact h1

theorem b3Forms_contMDiff_smoothTransition :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ Real.smoothTransition (3 * t - 1)) :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).contMDiff

/-- **The segment from `u` to `v` in the chart at `x`**, reparametrized to be tame.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_segPath (x : M) (u v : E) : ℝ → M :=
  fun t ↦ (chartAt E x).symm (u + Real.smoothTransition (3 * t - 1) • (v - u))

theorem b3Forms_segPath_mem {U : Set E} (hUc : Convex ℝ U) {u v : E} (hu : u ∈ U) (hv : v ∈ U)
    (t : ℝ) : u + Real.smoothTransition (3 * t - 1) • (v - u) ∈ U := by
  have := hUc.lineMap_mem hu hv ⟨Real.smoothTransition.nonneg (3 * t - 1),
    Real.smoothTransition.le_one (3 * t - 1)⟩
  rwa [AffineMap.lineMap_apply_module', add_comm] at this

theorem b3Forms_segPath_isTame (x : M) {U : Set E} (hUc : Convex ℝ U)
    (hU : U ⊆ (chartAt E x).target) {u v : E} (hu : u ∈ U) (hv : v ∈ U) :
    b3Forms_IsTame E (b3Forms_segPath x u v) := by
  refine ⟨?_, 1 / 3, by norm_num, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
        (fun t : ℝ ↦ u + Real.smoothTransition (3 * t - 1) • (v - u)) :=
      ((contDiff_const.add ((Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const)).smul contDiff_const))).contMDiff
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := x)).of_le (by norm_num)
      |>.comp_contMDiff hf
      fun t ↦ hU (b3Forms_segPath_mem hUc hu hv t)
  · simp only [b3Forms_segPath]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by norm_num)]
  · simp only [b3Forms_segPath]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by norm_num)]

theorem b3Forms_segPath_zero (x : M) (u v : E) :
    b3Forms_segPath x u v 0 = (chartAt E x).symm u := by
  simp only [b3Forms_segPath]
  rw [Real.smoothTransition.zero_of_nonpos (by norm_num)]
  simp

theorem b3Forms_segPath_one (x : M) (u v : E) :
    b3Forms_segPath x u v 1 = (chartAt E x).symm v := by
  simp only [b3Forms_segPath]
  rw [Real.smoothTransition.one_of_one_le (by norm_num)]
  simp

theorem b3Forms_chart_segPath (x : M) {U : Set E} (hUc : Convex ℝ U)
    (hU : U ⊆ (chartAt E x).target) {u v : E} (hu : u ∈ U) (hv : v ∈ U) (t : ℝ) :
    b3Forms_segPath x u v t ∈ (chartAt E x).source ∧
      chartAt E x (b3Forms_segPath x u v t) ∈ U := by
  have hm := b3Forms_segPath_mem hUc hu hv t
  refine ⟨(chartAt E x).map_target (hU hm), ?_⟩
  simp only [b3Forms_segPath]
  rwa [(chartAt E x).right_inv (hU hm)]

/-- **The line integral along a chart segment** through a local primitive. -/
theorem b3Forms_lineIntegral_segPath {α : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (x : M) {U : Set E} (hUc : Convex ℝ U) (hU : U ⊆ (chartAt E x).target) {h : E → ℝ}
    (hh : ∀ w ∈ U, HasFDerivAt h (b3Forms_toCLM (b3Forms_loc α x w)) w) {u v : E} (hu : u ∈ U)
    (hv : v ∈ U) : b3Forms_lineIntegral α (b3Forms_segPath x u v) 0 1 = h v - h u := by
  rw [b3Forms_lineIntegral_eq_of_primitive hα hh (b3Forms_segPath_isTame x hUc hU hu hv).1
    fun t _ ↦ b3Forms_chart_segPath x hUc hU hu hv t, b3Forms_segPath_zero, b3Forms_segPath_one,
    (chartAt E x).right_inv (hU hu), (chartAt E x).right_inv (hU hv)]

end Local

section Reach

/-- Every point has a neighbourhood whose points are reached from it by tame paths. -/
theorem b3Forms_exists_local_tame (q : M) :
    ∃ r > 0, Metric.ball (chartAt E q q) r ⊆ (chartAt E q).target ∧
      ∀ w ∈ Metric.ball (chartAt E q q) r,
        b3Forms_IsTame E (b3Forms_segPath q (chartAt E q q) w) ∧
          b3Forms_segPath q (chartAt E q q) w 0 = q ∧
          b3Forms_segPath q (chartAt E q q) w 1 = (chartAt E q).symm w := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (chartAt E q).open_target _
    ((chartAt E q).map_source (mem_chart_source E q))
  refine ⟨r, hr, hball, fun w hw ↦ ⟨b3Forms_segPath_isTame q (convex_ball _ _) hball
    (Metric.mem_ball_self hr) hw, ?_, b3Forms_segPath_one q _ _⟩⟩
  rw [b3Forms_segPath_zero, (chartAt E q).left_inv (mem_chart_source E q)]

theorem b3Forms_nhds_of_ball (q : M) {r : ℝ} (hr : 0 < r) :
    (chartAt E q).source ∩ chartAt E q ⁻¹' Metric.ball (chartAt E q q) r ∈ 𝓝 q :=
  inter_mem ((chartAt E q).open_source.mem_nhds (mem_chart_source E q))
    ((chartAt E q).continuousAt (mem_chart_source E q) (Metric.ball_mem_nhds _ hr))

theorem b3Forms_exists_tame_nhds (q : M) :
    ∃ V ∈ 𝓝 q, ∀ q' ∈ V, ∃ γ : ℝ → M, b3Forms_IsTame E γ ∧ γ 0 = q ∧ γ 1 = q' := by
  obtain ⟨r, hr, -, h⟩ := b3Forms_exists_local_tame (E := E) q
  refine ⟨_, b3Forms_nhds_of_ball (E := E) q hr, fun q' hq' ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := h _ hq'.2
  exact ⟨_, h1, h2, by rw [h3, (chartAt E q).left_inv hq'.1]⟩

theorem b3Forms_rev_zero (γ : ℝ → M) : b3Forms_rev γ 0 = γ 1 := by simp [b3Forms_rev]

theorem b3Forms_rev_one (γ : ℝ → M) : b3Forms_rev γ 1 = γ 0 := by simp [b3Forms_rev]

theorem b3Forms_concat_zero (γ δ : ℝ → M) : b3Forms_concat γ δ 0 = γ 0 := by
  simp [b3Forms_concat]

theorem b3Forms_concat_one (γ δ : ℝ → M) : b3Forms_concat γ δ 1 = δ 1 := by
  rw [b3Forms_concat, ite_eq_right (show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

/-- **A connected manifold is connected by tame paths.** -/
theorem b3Forms_reachable [ConnectedSpace M] (p₀ q : M) :
    ∃ γ : ℝ → M, b3Forms_IsTame E γ ∧ γ 0 = p₀ ∧ γ 1 = q := by
  set R := {q : M | ∃ γ : ℝ → M, b3Forms_IsTame E γ ∧ γ 0 = p₀ ∧ γ 1 = q}
  have hopen : IsOpen R := isOpen_iff_mem_nhds.2 fun q ⟨γ, hγ, h0, h1⟩ ↦ by
    obtain ⟨V, hV, hV'⟩ := b3Forms_exists_tame_nhds (E := E) q
    refine Filter.mem_of_superset hV fun q' hq' ↦ ?_
    obtain ⟨δ, hδ, hδ0, hδ1⟩ := hV' q' hq'
    exact ⟨_, hγ.concat hδ (h1.trans hδ0.symm), by rw [b3Forms_concat_zero, h0],
      by rw [b3Forms_concat_one, hδ1]⟩
  have hclosed : IsClosed R := isOpen_compl_iff.1 <| isOpen_iff_mem_nhds.2 fun q hq ↦ by
    obtain ⟨V, hV, hV'⟩ := b3Forms_exists_tame_nhds (E := E) q
    refine Filter.mem_of_superset hV fun q' hq' ⟨γ, hγ, h0, h1⟩ ↦ hq ?_
    obtain ⟨δ, hδ, hδ0, hδ1⟩ := hV' q' hq'
    exact ⟨_, hγ.concat hδ.rev (by rw [b3Forms_rev_zero, hδ1, h1]),
      by rw [b3Forms_concat_zero, h0], by rw [b3Forms_concat_one, b3Forms_rev_one, hδ0]⟩
  have hne : R.Nonempty := ⟨p₀, _, b3Forms_isTame_const p₀, rfl, rfl⟩
  have := (IsClopen.eq_univ ⟨hclosed, hopen⟩ hne)
  exact (this ▸ mem_univ q : q ∈ R)

end Reach

section Primitive

variable {α : M → E [⋀^Fin 1]→L[ℝ] ℝ}

/-- **Vanishing periods**: the line integral of `α` along every `C¹` loop is `0`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_PeriodsVanish (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) : Prop :=
  ∀ γ : ℝ → M, Function.Periodic γ 1 → ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ →
    b3Forms_lineIntegral α γ 0 1 = 0

/-- With vanishing periods, line integrals along tame paths depend only on the endpoints. -/
theorem b3Forms_lineIntegral_eq_of_endpoints (hα : b3Forms_IsSmooth α)
    (hper : b3Forms_PeriodsVanish α) {γ δ : ℝ → M} (hγ : b3Forms_IsTame E γ)
    (hδ : b3Forms_IsTame E δ) (h0 : γ 0 = δ 0) (h1 : γ 1 = δ 1) :
    b3Forms_lineIntegral α γ 0 1 = b3Forms_lineIntegral α δ 0 1 := by
  have hj : γ 1 = b3Forms_rev δ 0 := by rw [b3Forms_rev_zero, h1]
  have hc := hγ.concat hδ.rev hj
  have hcl : b3Forms_concat γ (b3Forms_rev δ) 0 = b3Forms_concat γ (b3Forms_rev δ) 1 := by
    rw [b3Forms_concat_zero, b3Forms_concat_one, b3Forms_rev_one, h0]
  have := hper _ (b3Forms_loopOf_periodic _) (hc.contMDiff_loopOf hcl)
  rw [b3Forms_lineIntegral_loopOf α hc hcl, b3Forms_lineIntegral_concat hα hγ hδ.rev hj,
    b3Forms_lineIntegral_rev α hδ.1] at this
  linarith

variable [ConnectedSpace M]

variable (α) in
/-- **The primitive** `q ↦ ∫_{p₀}^{q} α` along a chosen tame path from `p₀`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_prim (p₀ q : M) : ℝ :=
  b3Forms_lineIntegral α (b3Forms_reachable (E := E) p₀ q).choose 0 1

theorem b3Forms_prim_eq (hα : b3Forms_IsSmooth α) (hper : b3Forms_PeriodsVanish α) {p₀ q : M}
    {γ : ℝ → M} (hγ : b3Forms_IsTame E γ) (h0 : γ 0 = p₀) (h1 : γ 1 = q) :
    b3Forms_prim α p₀ q = b3Forms_lineIntegral α γ 0 1 := by
  obtain ⟨h1', h2', h3'⟩ := (b3Forms_reachable (E := E) p₀ q).choose_spec
  exact b3Forms_lineIntegral_eq_of_endpoints hα hper h1' hγ (h2'.trans h0.symm)
    (h3'.trans h1.symm)

theorem b3Forms_prim_step (hα : b3Forms_IsSmooth α) (hper : b3Forms_PeriodsVanish α)
    (p₀ : M) {δ : ℝ → M} (hδ : b3Forms_IsTame E δ) :
    b3Forms_prim α p₀ (δ 1) = b3Forms_prim α p₀ (δ 0) + b3Forms_lineIntegral α δ 0 1 := by
  obtain ⟨h1', h2', h3'⟩ := (b3Forms_reachable (E := E) p₀ (δ 0)).choose_spec
  rw [b3Forms_prim_eq hα hper (h1'.concat hδ h3') (by rw [b3Forms_concat_zero, h2'])
    (b3Forms_concat_one _ _), b3Forms_lineIntegral_concat hα h1' hδ h3']
  rfl

/-- **The primitive in a chart ball**: it differs from a local primitive by a constant. -/
theorem b3Forms_prim_chart (hα : b3Forms_IsSmooth α) (hdα : b3Forms_d α = 0)
    (hper : b3Forms_PeriodsVanish α) (p₀ x : M) {w₀ : E} {r : ℝ}
    (hball : Metric.ball w₀ r ⊆ (chartAt E x).target) :
    ∃ h : E → ℝ, (∀ w ∈ Metric.ball w₀ r, HasFDerivAt h (b3Forms_toCLM (b3Forms_loc α x w)) w) ∧
      ∀ w ∈ Metric.ball w₀ r,
        b3Forms_prim α p₀ ((chartAt E x).symm w) =
          b3Forms_prim α p₀ ((chartAt E x).symm w₀) + h w - h w₀ := by
  rcases (Metric.ball w₀ r).eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp [he], by simp [he]⟩
  have hr : 0 < r := Metric.nonempty_ball.1 hne
  obtain ⟨h, hh⟩ := b3Forms_exists_local_primitive hα hdα x (convex_ball w₀ r)
    Metric.isOpen_ball hball
  refine ⟨h, hh, fun w hw ↦ ?_⟩
  have hδ := b3Forms_segPath_isTame x (convex_ball w₀ r) hball (Metric.mem_ball_self hr) hw
  have := b3Forms_prim_step hα hper p₀ hδ
  rw [b3Forms_segPath_zero, b3Forms_segPath_one, b3Forms_lineIntegral_segPath hα x
    (convex_ball w₀ r) hball hh (Metric.mem_ball_self hr) hw] at this
  rw [this]
  ring

theorem b3Forms_contDiffOn_toCLM_loc (hα : b3Forms_IsSmooth α) (x : M) :
    ContDiffOn ℝ ∞ (fun w ↦ b3Forms_toCLM (b3Forms_loc α x w)) (chartAt E x).target :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv
    |>.contDiff.comp_contDiffOn (hα x)

/-- **The primitive has the right derivative in charts.** -/
theorem b3Forms_hasFDerivAt_prim (hα : b3Forms_IsSmooth α) (hdα : b3Forms_d α = 0)
    (hper : b3Forms_PeriodsVanish α) (p₀ x : M) {w₀ : E} (hw₀ : w₀ ∈ (chartAt E x).target) :
    (∀ᶠ w in 𝓝 w₀, HasFDerivAt (b3Forms_prim α p₀ ∘ (chartAt E x).symm)
      (b3Forms_toCLM (b3Forms_loc α x w)) w) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target _ hw₀
  obtain ⟨h, hh, heq⟩ := b3Forms_prim_chart hα hdα hper p₀ x hball
  filter_upwards [Metric.ball_mem_nhds w₀ hr] with w hw
  have hO : Metric.ball w₀ r ∈ 𝓝 w := Metric.isOpen_ball.mem_nhds hw
  refine ((hh w hw).const_add (b3Forms_prim α p₀ ((chartAt E x).symm w₀) - h w₀))
    |>.congr_of_eventuallyEq ?_
  filter_upwards [hO] with v hv
  simp only [Function.comp_apply, heq v hv]
  ring

/-- **De Rham's theorem in degree one for loops**: on a connected manifold, a smooth closed
`1`-form whose periods along all `C¹` loops vanish is the differential of a smooth function. -/
theorem b3Forms_exists_primitive (hα : b3Forms_IsSmooth α) (hdα : b3Forms_d α = 0)
    (hper : b3Forms_PeriodsVanish α) :
    ∃ g : M → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) g) ∧
      b3Forms_d (b3Forms_fun (E := E) g) = α := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty M)
  refine ⟨b3Forms_prim α p₀, ?_, ?_⟩
  · rw [b3Forms_isSmooth_fun_iff]
    intro x w₀ hw₀
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (chartAt E x).open_target _ hw₀
    have hev := b3Forms_hasFDerivAt_prim hα hdα hper p₀ x hw₀
    have hO : IsOpen (Metric.ball w₀ r) := Metric.isOpen_ball
    have hd : ∀ w ∈ Metric.ball w₀ r, HasFDerivAt (b3Forms_prim α p₀ ∘ (chartAt E x).symm)
        (b3Forms_toCLM (b3Forms_loc α x w)) w := fun w hw ↦
      (b3Forms_hasFDerivAt_prim hα hdα hper p₀ x (hball hw)).self_of_nhds
    have hsm : ContDiffOn ℝ ∞ (b3Forms_prim α p₀ ∘ (chartAt E x).symm) (Metric.ball w₀ r) := by
      rw [contDiffOn_infty_iff_fderiv_of_isOpen hO]
      refine ⟨fun w hw ↦ (hd w hw).differentiableAt.differentiableWithinAt, ?_⟩
      exact ((b3Forms_contDiffOn_toCLM_loc hα x).mono hball).congr fun w hw ↦ (hd w hw).fderiv
    exact (hsm.contDiffAt (Metric.ball_mem_nhds w₀ hr)).contDiffWithinAt
  · funext z
    have hz := (chartAt E z).map_source (mem_chart_source E z)
    rw [b3Forms_d_fun, (b3Forms_hasFDerivAt_prim hα hdα hper p₀ z hz).self_of_nhds.fderiv,
      b3Forms_toCLM]
    exact ((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).apply_symm_apply _).trans
      (b3Forms_loc_self α z)

end Primitive

section PeriodMap

variable (E M) in
/-- **The `C¹` loops** of `M`: `1`-periodic `C¹` maps `ℝ → M` (as `b3_SmoothLoop`).
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_Loop : Type _ :=
  {γ : ℝ → M // Function.Periodic γ 1 ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ}

/-- The periods of closed `1`-forms along loops. -/
def b3Forms_periodClosed : b3Forms_closed E M 0 →ₗ[ℝ] (b3Forms_Loop E M → ℝ) where
  toFun α γ := b3Forms_lineIntegral α.1.1 γ.1 0 1
  map_add' α β := by
    funext γ
    exact b3Forms_lineIntegral_add α.1.2 β.1.2 γ.2.2 0 1
  map_smul' c α := by
    funext γ
    exact b3Forms_lineIntegral_smul c α.1.1 γ.1 0 1

/-- Exact forms have vanishing periods along loops. -/
theorem b3Forms_periodClosed_exact (α : b3Forms_closed E M 0)
    (hα : α ∈ (b3Forms_exact E M 0).comap (b3Forms_closed E M 0).subtype) :
    b3Forms_periodClosed α = 0 := by
  obtain ⟨γ₀, hγ₀⟩ := hα
  have h : α.1.1 = b3Forms_d (b3Forms_fun (E := E) (b3Forms_toFun γ₀.1)) := by
    rw [b3Forms_fun_toFun]
    exact (congrArg Subtype.val hγ₀).symm
  have hs : b3Forms_IsSmooth (b3Forms_fun (E := E) (b3Forms_toFun γ₀.1)) := by
    rw [b3Forms_fun_toFun]; exact γ₀.2
  funext γ
  show b3Forms_lineIntegral α.1.1 γ.1 0 1 = 0
  rw [h, b3Forms_lineIntegral_d hs γ.2.2]
  have : γ.1 1 = γ.1 0 := by simpa using γ.2.1 0
  rw [this, sub_self]

/-- **The period map** `H¹_dR(M) → (loops → ℝ)`, `[α] ↦ (γ ↦ ∫_γ α)`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (conservative covector
fields) and Ch. 17 (de Rham's theorem in degree one); Forster, *Lectures on Riemann Surfaces*, GTM
81, §10. -/
def b3Forms_periodMap : b3Forms_deRham E M 0 →ₗ[ℝ] (b3Forms_Loop E M → ℝ) :=
  ((b3Forms_exact E M 0).comap (b3Forms_closed E M 0).subtype).liftQ b3Forms_periodClosed
    fun α hα ↦ b3Forms_periodClosed_exact α hα

theorem b3Forms_periodMap_mk (α : b3Forms_closed E M 0) (γ : b3Forms_Loop E M) :
    b3Forms_periodMap (Submodule.Quotient.mk α) γ = b3Forms_lineIntegral α.1.1 γ.1 0 1 := rfl

/-- **De Rham's theorem in degree one for loops**: on a connected manifold the period map
`H¹_dR(M) → (loops → ℝ)` is injective; closed `1`-forms modulo exact forms are detected by their
periods along `C¹` loops. -/
theorem b3Forms_periodMap_injective [ConnectedSpace M] :
    Function.Injective (b3Forms_periodMap (E := E) (M := M)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  induction c using Submodule.Quotient.induction_on with
  | H α =>
    rw [Submodule.Quotient.mk_eq_zero]
    have hper : b3Forms_PeriodsVanish α.1.1 := fun γ hγ hγ' ↦
      congrFun hc ⟨γ, hγ, hγ'⟩
    obtain ⟨g, hg, hgα⟩ := b3Forms_exists_primitive α.1.2
      (congrArg Subtype.val (LinearMap.mem_ker.1 α.2)) hper
    exact ⟨⟨b3Forms_fun g, hg⟩, Subtype.ext hgα⟩

end PeriodMap

end HodgeLean.Foundations.Program
