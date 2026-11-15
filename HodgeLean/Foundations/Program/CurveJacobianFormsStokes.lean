import HodgeLean.Foundations.Program.CurveJacobianFormsIntegral

/-!
# Track B3 foundations (stage B3.6b): Stokes' theorem on a compact manifold without boundary

* `b3Forms_integral_extDeriv_eq_zero`: on a real space with a basis, the integral of the exterior
  derivative of a compactly supported `C¹` form vanishes (integration by parts, coordinate by
  coordinate);
* `b3Forms_tsupport_d_subset`: the exterior derivative does not enlarge supports;
* `b3Forms_chartIntegral_d_eq_zero`: the same in a chart, for a form supported in the chart;
* `b3Forms_integral_d_eq_zero`: **Stokes' theorem** `∫_M dβ = 0` for a smooth `n - 1`-form `β` on
  a compact manifold with an oriented atlas (no boundary: the model is a whole vector space). -/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Function
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The integral of a directional derivative of a compactly supported `C¹` function vanishes. -/
theorem b3Forms_integral_fderiv_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure] {h : E → ℝ}
    (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (w : E) :
    ∫ u, fderiv ℝ h u w ∂μ = 0 := by
  have hcont : Continuous fun u ↦ fderiv ℝ h u w :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h1 : Integrable (fun u ↦ fderiv ℝ (fun _ : E ↦ (1 : ℝ)) u w * h u) μ := by simp
  have h2 : Integrable (fun u ↦ (fun _ : E ↦ (1 : ℝ)) u * fderiv ℝ h u w) μ := by
    simpa using hcont.integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) w)
  have h3 : Integrable (fun u ↦ (fun _ : E ↦ (1 : ℝ)) u * h u) μ := by
    simpa using hh.continuous.integrable_of_hasCompactSupport hc
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun _ _ ↦ differentiableAt_const _) (fun u _ ↦ (hh.differentiable one_ne_zero) u)
  simpa using this

/-- **Stokes' theorem on a vector space**: for a compactly supported `C¹` `k`-form `g` on a space
with a basis of `k + 1` vectors, the integral of `dg` evaluated on the basis vanishes. -/
theorem b3Forms_integral_extDeriv_eq_zero {k : ℕ} (b : Module.Basis (Fin (k + 1)) ℝ E)
    {g : E → E [⋀^Fin k]→L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    ∫ u, extDeriv g u b ∂b.addHaar = 0 := by
  have hd : ∀ u, extDeriv g u b =
      ∑ i : Fin (k + 1), (-1) ^ i.val • fderiv ℝ (fun x ↦ g x (i.removeNth b)) u (b i) :=
    fun u ↦ extDeriv_apply ((hg.differentiable one_ne_zero) u) b
  simp_rw [hd]
  have hci : ∀ i : Fin (k + 1), ContDiff ℝ 1 (fun x ↦ g x (i.removeNth b)) := fun i ↦
    (ContinuousAlternatingMap.apply ℝ E ℝ (i.removeNth b)).contDiff.comp hg
  have hcc : ∀ i : Fin (k + 1), HasCompactSupport (fun x ↦ g x (i.removeNth b)) := fun i ↦
    hc.comp_left (g := fun A : E [⋀^Fin k]→L[ℝ] ℝ ↦ A (i.removeNth b)) rfl
  simp_rw [zsmul_eq_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_const_mul, b3Forms_integral_fderiv_eq_zero _ (hci i) (hcc i), mul_zero]
  · intro i _
    refine Integrable.const_mul ?_ _
    exact ((hci i).continuous_fderiv one_ne_zero).clm_apply continuous_const
      |>.integrable_of_hasCompactSupport ((hcc i).fderiv_apply (𝕜 := ℝ) _)

end Flat

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {k : ℕ}

theorem b3Forms_extDeriv_eventuallyEq_zero {g : E → E [⋀^Fin k]→L[ℝ] ℝ} {u : E}
    (h : g =ᶠ[𝓝 u] 0) : extDeriv g u = 0 := by
  rw [h.extDeriv_eq]
  simp only [extDeriv, Pi.zero_apply, fderiv_zero]
  exact (alternatizeUncurryFinCLM ℝ E ℝ).map_zero

/-- **The exterior derivative does not enlarge supports.** -/
theorem b3Forms_tsupport_d_subset (γ : M → E [⋀^Fin k]→L[ℝ] ℝ) :
    tsupport (b3Forms_d γ) ⊆ tsupport γ := by
  refine closure_minimal (fun z hz ↦ ?_) (isClosed_tsupport γ)
  by_contra h
  apply hz
  have h0 : ∀ᶠ w in 𝓝 z, γ w = 0 := (notMem_tsupport_iff_eventuallyEq.1 h)
  have hz' := (chartAt E z).map_source (mem_chart_source E z)
  have h1 : ∀ᶠ u in 𝓝 (chartAt E z z), γ ((chartAt E z).symm u) = 0 := by
    have := (chartAt E z).continuousAt_symm hz'
    rw [ContinuousAt, (chartAt E z).left_inv (mem_chart_source E z)] at this
    exact this.eventually h0
  refine b3Forms_extDeriv_eventuallyEq_zero ?_
  filter_upwards [h1] with u hu
  ext v
  simp [b3Forms_loc, hu]

/-- The local representative of a form supported in the chart, extended by `0`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_locExt (γ : M → E [⋀^Fin k]→L[ℝ] ℝ) (x : M) : E → E [⋀^Fin k]→L[ℝ] ℝ :=
  (chartAt E x).target.indicator (b3Forms_loc γ x)

theorem b3Forms_support_locExt_subset (γ : M → E [⋀^Fin k]→L[ℝ] ℝ) (x : M) :
    support (b3Forms_locExt γ x) ⊆ chartAt E x '' ((chartAt E x).source ∩ support γ) := by
  intro u hu
  simp only [b3Forms_locExt, mem_support, indicator_apply_ne_zero] at hu
  obtain ⟨hut, hne⟩ := hu
  refine ⟨(chartAt E x).symm u, ⟨(chartAt E x).map_target hut, ?_⟩, (chartAt E x).right_inv hut⟩
  intro h0
  apply hne
  ext v
  simp [b3Forms_loc, h0]

variable [T2Space M]

theorem b3Forms_locExt_eventuallyEq_zero {γ : M → E [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (hc : IsCompact (tsupport γ)) (hx : tsupport γ ⊆ (chartAt E x).source) {u : E}
    (hu : u ∉ (chartAt E x).target) : b3Forms_locExt γ x =ᶠ[𝓝 u] 0 := by
  have hK : IsCompact (chartAt E x '' tsupport γ) :=
    hc.image_of_continuousOn ((chartAt E x).continuousOn.mono hx)
  have hKt : chartAt E x '' tsupport γ ⊆ (chartAt E x).target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (chartAt E x).map_source (hx hz)
  filter_upwards [hK.isClosed.isOpen_compl.mem_nhds fun h ↦ hu (hKt h)] with v hv
  by_contra h
  obtain ⟨z, ⟨_, hz⟩, rfl⟩ := b3Forms_support_locExt_subset γ x h
  exact hv ⟨z, subset_tsupport γ hz, rfl⟩

theorem b3Forms_hasCompactSupport_locExt {γ : M → E [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (hc : IsCompact (tsupport γ)) (hx : tsupport γ ⊆ (chartAt E x).source) :
    HasCompactSupport (b3Forms_locExt γ x) := by
  have hK : IsCompact (chartAt E x '' tsupport γ) :=
    hc.image_of_continuousOn ((chartAt E x).continuousOn.mono hx)
  refine hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ hK.isClosed)
  exact (b3Forms_support_locExt_subset γ x).trans
    (image_mono (inter_subset_right.trans (subset_tsupport γ)))

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem b3Forms_contDiff_locExt {γ : M → E [⋀^Fin k]→L[ℝ] ℝ} (hγ : b3Forms_IsSmooth γ) {x : M}
    (hc : IsCompact (tsupport γ)) (hx : tsupport γ ⊆ (chartAt E x).source) :
    ContDiff ℝ ∞ (b3Forms_locExt γ x) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ (chartAt E x).target
  · refine (hγ.contDiffAt hu).congr_of_eventuallyEq ?_
    filter_upwards [(chartAt E x).open_target.mem_nhds hu] with v hv
    simp [b3Forms_locExt, hv]
  · exact contDiffAt_const.congr_of_eventuallyEq (b3Forms_locExt_eventuallyEq_zero hc hx hu)

/-- **The exterior derivative in a chart, extended by zero.** -/
theorem b3Forms_chartFun_d (b : Module.Basis (Fin (k + 1)) ℝ E)
    {γ : M → E [⋀^Fin k]→L[ℝ] ℝ} (hγ : b3Forms_IsSmooth γ) {x : M}
    (hc : IsCompact (tsupport γ)) (hx : tsupport γ ⊆ (chartAt E x).source) :
    b3Forms_chartFun b x (b3Forms_d γ) = fun u ↦ extDeriv (b3Forms_locExt γ x) u b := by
  funext u
  by_cases hu : u ∈ (chartAt E x).target
  · have h : b3Forms_locExt γ x =ᶠ[𝓝 u] b3Forms_loc γ x := by
      filter_upwards [(chartAt E x).open_target.mem_nhds hu] with v hv
      simp [b3Forms_locExt, hv]
    rw [h.extDeriv_eq]
    simp only [b3Forms_chartFun, indicator_of_mem hu]
    rw [b3Forms_loc_d hγ x hu]
  · rw [b3Forms_extDeriv_eventuallyEq_zero (b3Forms_locExt_eventuallyEq_zero hc hx hu)]
    simp [b3Forms_chartFun, hu]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Stokes' theorem in a chart.** -/
theorem b3Forms_chartIntegral_d_eq_zero (b : Module.Basis (Fin (k + 1)) ℝ E)
    {γ : M → E [⋀^Fin k]→L[ℝ] ℝ} (hγ : b3Forms_IsSmooth γ) {x : M}
    (hc : IsCompact (tsupport γ)) (hx : tsupport γ ⊆ (chartAt E x).source) :
    b3Forms_chartIntegral b x (b3Forms_d γ) = 0 := by
  rw [b3Forms_chartIntegral, b3Forms_chartFun_d b hγ hc hx]
  exact b3Forms_integral_extDeriv_eq_zero b ((b3Forms_contDiff_locExt hγ hc hx).of_le
    (by exact_mod_cast le_top)) (b3Forms_hasCompactSupport_locExt hc hx)

theorem b3Forms_d_finsetSum {ι : Type*} (S : Finset ι) {β : ι → M → E [⋀^Fin k]→L[ℝ] ℝ}
    (hβ : ∀ i ∈ S, b3Forms_IsSmooth (β i)) :
    b3Forms_d (∑ i ∈ S, β i) = ∑ i ∈ S, b3Forms_d (β i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using b3Forms_d_smul (M := M) 0 (0 : M → E [⋀^Fin k]→L[ℝ] ℝ)
  | insert j S hj ih =>
    have hS : ∀ i ∈ S, b3Forms_IsSmooth (β i) := fun i hi ↦ hβ i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hj, Finset.sum_insert hj, b3Forms_d_add
      (hβ j (Finset.mem_insert_self j S)) ((b3Forms_Ω E M k).sum_mem hS), ih hS]

variable [CompactSpace M]

/-- **Stokes' theorem** on a compact manifold without boundary with an oriented atlas:
`∫_M dβ = 0` for every smooth `n - 1`-form `β`. -/
theorem b3Forms_integral_d_eq_zero (hor : b3Forms_Oriented E M)
    (b : Module.Basis (Fin (k + 1)) ℝ E) {β : M → E [⋀^Fin k]→L[ℝ] ℝ}
    (hβ : b3Forms_IsSmooth β) : b3Forms_integral b (b3Forms_d β) = 0 := by
  have hsm : ∀ i ∈ b3Forms_pouSupp E M,
      b3Forms_IsSmooth (b3Forms_smulFun (b3Forms_pou E M i) β) := fun i _ ↦ hβ.smulFun_pou i
  rw [← b3Forms_sum_smulFun_pou β, b3Forms_d_finsetSum _ hsm,
    b3Forms_integral_finsetSum b _ fun i hi ↦ (hsm i hi).d]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hsub : tsupport (b3Forms_smulFun (b3Forms_pou E M i) β) ⊆ (chartAt E i).source :=
    (b3Forms_tsupport_smulFun_subset_left _ _).trans (b3Forms_pou_isSubordinate i)
  rw [b3Forms_integral_eq_chartIntegral b hor (hsm i hi).d
    ((b3Forms_tsupport_d_subset _).trans hsub)]
  exact b3Forms_chartIntegral_d_eq_zero b (hsm i hi) (b3Forms_isCompact_tsupport _) hsub

end Manifold

end HodgeLean.Foundations.Program
