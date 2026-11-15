import HodgeLean.Foundations.Program.CurveJacobianFormsPairing

/-!
# Track B3 foundations (stage B3.6b): line integrals of `1`-forms along `C¹` paths

* `b3Forms_velocity γ t`, Mathlib's `mfderiv` of a path applied to `1` (the velocity of
  `b3_velocity`), and its expression in any chart (`b3Forms_deriv_chart_comp`);
* `b3Forms_lineIntegral α γ a b = ∫_a^b α(γ t)(γ' t) dt`, its integrand in a chart
  (`b3Forms_apply_velocity_eq_loc`), its continuity, and its linearity in the form;
* the fundamental theorem of calculus `∫_γ dg = g(γ b) - g(γ a)` (`b3Forms_lineIntegral_d`): exact
  forms have zero periods along loops.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Function
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Velocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- **The velocity** of a path `γ : ℝ → M` at `t`, in the coordinates of the chart at `γ t`
(Mathlib's `mfderiv` applied to `1`, as in `b3_velocity`).
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (line integrals of
covector fields); Mathlib `mfderiv`. -/
def b3Forms_velocity (γ : ℝ → M) (t : ℝ) : E :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1

theorem b3Forms_velocity_eq {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    b3Forms_velocity γ t = deriv (chartAt E (γ t) ∘ γ) t := by
  rw [b3Forms_velocity, hγ.mfderiv]
  change fderivWithin ℝ (writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) t γ) (range 𝓘(ℝ, ℝ))
    (extChartAt 𝓘(ℝ, ℝ) t t) 1 = _
  rw [modelWithCornersSelf_coe, range_id, fderivWithin_univ, extChartAt_model_space_eq_id]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, extChartAt_coe, modelWithCornersSelf_coe, id_eq, CompTriple.comp_eq,
    deriv]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem b3Forms_contDiffOn_chart_comp {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (x : M) :
    ContDiffOn ℝ 1 (chartAt E x ∘ γ) (γ ⁻¹' (chartAt E x).source) := by
  have := ((contMDiff_iff (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (n := 1)).1 hγ).2 0 x
  simpa [extChartAt, Function.comp_def] using this

theorem b3Forms_isOpen_preimage_source {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (x : M) : IsOpen (γ ⁻¹' (chartAt E x).source) :=
  hγ.continuous.isOpen_preimage _ (chartAt E x).open_source

theorem b3Forms_hasDerivAt_chart_comp {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    {x : M} {t : ℝ} (ht : γ t ∈ (chartAt E x).source) :
    HasDerivAt (chartAt E x ∘ γ) (deriv (chartAt E x ∘ γ) t) t :=
  (((b3Forms_contDiffOn_chart_comp hγ x).contDiffAt
    ((b3Forms_isOpen_preimage_source hγ x).mem_nhds ht)).differentiableAt
    (by simp)).hasDerivAt

/-- The velocity read in another chart. -/
theorem b3Forms_deriv_chart_comp {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    {x : M} {t : ℝ} (ht : γ t ∈ (chartAt E x).source) :
    deriv (chartAt E x ∘ γ) t =
      fderiv ℝ (b3Forms_tr (γ t) x) (chartAt E (γ t) (γ t)) (b3Forms_velocity γ t) := by
  set z := γ t
  have hz : chartAt E z z ∈ b3Forms_trDom z x :=
    ⟨(chartAt E z).map_source (mem_chart_source E z), by
      rw [mem_preimage, (chartAt E z).left_inv (mem_chart_source E z)]; exact ht⟩
  have h1 : chartAt E x ∘ γ =ᶠ[𝓝 t] b3Forms_tr z x ∘ (chartAt E z ∘ γ) := by
    filter_upwards [(b3Forms_isOpen_preimage_source hγ z).mem_nhds
      (show γ t ∈ (chartAt E z).source from mem_chart_source E z)] with s hs
    simp only [Function.comp_apply, b3Forms_tr]
    rw [(chartAt E z).left_inv hs]
  have h2 := (b3Forms_differentiableAt_tr hz).hasFDerivAt.comp_hasDerivAt t
    (b3Forms_hasDerivAt_chart_comp hγ (mem_chart_source E z))
  rw [h1.deriv_eq, h2.deriv, b3Forms_velocity_eq (hγ.mdifferentiableAt one_ne_zero)]

/-- **The integrand of a line integral in a chart.** -/
theorem b3Forms_apply_velocity_eq_loc {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) {x : M} {t : ℝ} (ht : γ t ∈ (chartAt E x).source) :
    α (γ t) (fun _ ↦ b3Forms_velocity γ t) =
      b3Forms_loc α x (chartAt E x (γ t)) (fun _ ↦ deriv (chartAt E x ∘ γ) t) := by
  set z := γ t
  have hu : chartAt E z z ∈ b3Forms_trDom z x :=
    ⟨(chartAt E z).map_source (mem_chart_source E z), by
      rw [mem_preimage, (chartAt E z).left_inv (mem_chart_source E z)]; exact ht⟩
  have hc := b3Forms_fderiv_tr_comp (z := z) hu
    (by rw [(chartAt E z).left_inv (mem_chart_source E z)]; exact mem_chart_source E z)
  rw [b3Forms_fderiv_tr_self ((chartAt E z).map_source (mem_chart_source E z))] at hc
  have htr : b3Forms_tr z x (chartAt E z z) = chartAt E x z := by
    simp [b3Forms_tr, (chartAt E z).left_inv (mem_chart_source E z)]
  rw [htr] at hc
  rw [b3Forms_loc_chart α ht, compContinuousLinearMap_apply, b3Forms_deriv_chart_comp hγ ht]
  congr 1
  funext _
  have := congrArg (fun L : E →L[ℝ] E ↦ L (b3Forms_velocity γ t)) hc
  simpa using this

end Velocity

section LineIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The line integral** `∫_a^b α(γ t)(γ'(t)) dt` of a `1`-form along a path.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 11 (line integrals of
covector fields); Mathlib `mfderiv`. -/
def b3Forms_lineIntegral (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, α (γ t) (fun _ ↦ b3Forms_velocity γ t)

theorem b3Forms_continuous_apply_const :
    Continuous fun p : (E [⋀^Fin 1]→L[ℝ] ℝ) × E ↦ p.1 (fun _ ↦ p.2) := by
  have : (fun p : (E [⋀^Fin 1]→L[ℝ] ℝ) × E ↦ p.1 (fun _ ↦ p.2)) =
      fun p ↦ ((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm p.1) p.2 := by
    funext p
    rfl
  rw [this]
  exact ((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm.continuous.comp
    continuous_fst).clm_apply continuous_snd

/-- The integrand of a line integral of a smooth form along a `C¹` path is continuous. -/
theorem b3Forms_continuous_lineIntegrand {α : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    Continuous fun t ↦ α (γ t) (fun _ ↦ b3Forms_velocity γ t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set x := γ t₀
  have hO := (b3Forms_isOpen_preimage_source hγ x).mem_nhds (mem_chart_source E x)
  have heq : (fun t ↦ α (γ t) (fun _ ↦ b3Forms_velocity γ t)) =ᶠ[𝓝 t₀]
      fun t ↦ b3Forms_loc α x (chartAt E x (γ t)) (fun _ ↦ deriv (chartAt E x ∘ γ) t) := by
    filter_upwards [hO] with t ht
    exact b3Forms_apply_velocity_eq_loc hγ α ht
  refine ContinuousAt.congr ?_ heq.symm
  have h0 : ContinuousAt (b3Forms_loc α x) (chartAt E x (γ t₀)) :=
    (hα x).continuousOn.continuousAt ((chartAt E x).open_target.mem_nhds
      ((chartAt E x).map_source (mem_chart_source E x)))
  have h1 : ContinuousAt (fun t ↦ b3Forms_loc α x (chartAt E x (γ t))) t₀ :=
    h0.comp (f := chartAt E x ∘ γ)
      ((b3Forms_contDiffOn_chart_comp hγ x).continuousOn.continuousAt hO)
  have h2 : ContinuousAt (deriv (chartAt E x ∘ γ)) t₀ :=
    ((b3Forms_contDiffOn_chart_comp hγ x).continuousOn_deriv_of_isOpen
      (b3Forms_isOpen_preimage_source hγ x) le_rfl).continuousAt hO
  exact b3Forms_continuous_apply_const.continuousAt.comp (h1.prodMk h2)

theorem b3Forms_intervalIntegrable_lineIntegrand {α : M → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ α (γ t) (fun _ ↦ b3Forms_velocity γ t)) volume a b :=
  (b3Forms_continuous_lineIntegrand hα hγ).intervalIntegrable a b

/-- **The chain rule along a path**: `(g ∘ γ)' = dg(γ')`. -/
theorem b3Forms_hasDerivAt_comp {g : M → ℝ} (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (t : ℝ) :
    HasDerivAt (g ∘ γ)
      (b3Forms_d (b3Forms_fun (E := E) g) (γ t) (fun _ ↦ b3Forms_velocity γ t)) t := by
  set z := γ t
  have hz := (chartAt E z).map_source (mem_chart_source E z)
  have hgd : DifferentiableAt ℝ (g ∘ (chartAt E z).symm) (chartAt E z z) :=
    (((b3Forms_isSmooth_fun_iff g).1 hg z).contDiffAt
      ((chartAt E z).open_target.mem_nhds hz)).differentiableAt (by simp)
  have h1 : g ∘ γ =ᶠ[𝓝 t] (g ∘ (chartAt E z).symm) ∘ (chartAt E z ∘ γ) := by
    filter_upwards [(b3Forms_isOpen_preimage_source hγ z).mem_nhds
      (show γ t ∈ (chartAt E z).source from mem_chart_source E z)] with s hs
    simp only [Function.comp_apply]
    rw [(chartAt E z).left_inv hs]
  have h2 := hgd.hasFDerivAt.comp_hasDerivAt t
    (b3Forms_hasDerivAt_chart_comp hγ (mem_chart_source E z))
  rw [b3Forms_d_fun, ofSubsingleton_apply_apply,
    b3Forms_velocity_eq (hγ.mdifferentiableAt one_ne_zero)]
  exact h2.congr_of_eventuallyEq h1

/-- **The fundamental theorem of calculus for line integrals**: `∫_γ dg = g(γ b) - g(γ a)`. -/
theorem b3Forms_lineIntegral_d {g : M → ℝ} (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (a b : ℝ) :
    b3Forms_lineIntegral (b3Forms_d (b3Forms_fun (E := E) g)) γ a b = g (γ b) - g (γ a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ b3Forms_hasDerivAt_comp hg hγ t)
    (b3Forms_intervalIntegrable_lineIntegrand hg.d hγ a b)

theorem b3Forms_lineIntegral_add {α β : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hβ : b3Forms_IsSmooth β) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (a b : ℝ) :
    b3Forms_lineIntegral (α + β) γ a b =
      b3Forms_lineIntegral α γ a b + b3Forms_lineIntegral β γ a b := by
  simp only [b3Forms_lineIntegral, Pi.add_apply, ContinuousAlternatingMap.add_apply]
  exact intervalIntegral.integral_add (b3Forms_intervalIntegrable_lineIntegrand hα hγ a b)
    (b3Forms_intervalIntegrable_lineIntegrand hβ hγ a b)

theorem b3Forms_lineIntegral_smul (c : ℝ) (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) (γ : ℝ → M) (a b : ℝ) :
    b3Forms_lineIntegral (c • α) γ a b = c * b3Forms_lineIntegral α γ a b := by
  simp only [b3Forms_lineIntegral, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  exact intervalIntegral.integral_const_mul c _

end LineIntegral

end HodgeLean.Foundations.Program
