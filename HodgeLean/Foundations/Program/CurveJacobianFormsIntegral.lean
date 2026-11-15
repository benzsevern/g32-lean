import HodgeLean.Foundations.Program.CurveJacobianFormsOps

/-!
# Track B3 foundations (stage B3.6a): integration of top-degree forms

Let `M` be a manifold modelled on a real space `E` with a basis `b : Basis (Fin n) ℝ E`, which
fixes an orientation of `E` and the Lebesgue measure `b.addHaar`. An `n`-form `α` is integrated
* in one chart, `b3Forms_chartIntegral b x α = ∫ (loc α x)(b) d(b.addHaar)` over the chart image;
* over a compact manifold with an oriented atlas (`b3Forms_Oriented`: the changes of coordinates
  have positive Jacobian), as `∑ᶠ i, ∫_{chart i} ρᵢ α` for a smooth partition of unity `ρ`
  subordinate to the chart domains.

The change of variables formula (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`)
shows that chart integrals of a form supported in two charts agree
(`b3Forms_chartIntegral_eq_of_tsupport_subset`), from which the global integral agrees with the
chart integral of a form supported in one chart and does not depend on the partition of unity.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Function
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- An alternating `n`-form on an `n`-dimensional space pulled back along `L` is multiplied by
`det L` on a basis. -/
theorem b3Forms_comp_apply_basis (b : Module.Basis (Fin n) ℝ E) (A : E [⋀^Fin n]→L[ℝ] ℝ)
    (L : E →L[ℝ] E) :
    A.compContinuousLinearMap L b = LinearMap.det (L : E →ₗ[ℝ] E) * A b := by
  rw [compContinuousLinearMap_apply]
  have h := A.toAlternatingMap.eq_smul_basis_det b
  have h1 : A (⇑L ∘ ⇑b) = (A.toAlternatingMap b • b.det) (⇑L ∘ ⇑b) := by
    conv_lhs => rw [show A (⇑L ∘ ⇑b) = A.toAlternatingMap (⇑L ∘ ⇑b) from rfl, h]
  rw [h1, _root_.smul_apply, smul_eq_mul, show (⇑L ∘ ⇑b) = (L : E →ₗ[ℝ] E) ∘ b from rfl,
    b.det_comp, b.det_self, mul_one, mul_comm]
  rfl

end Det

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ E)

/-- **The density of an `n`-form in a chart**: the local representative evaluated on the basis,
extended by `0` outside the chart image.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_chartFun (x : M) (α : M → E [⋀^Fin n]→L[ℝ] ℝ) : E → ℝ :=
  (chartAt E x).target.indicator fun u ↦ b3Forms_loc α x u b

theorem b3Forms_chartFun_add (x : M) (α β : M → E [⋀^Fin n]→L[ℝ] ℝ) :
    b3Forms_chartFun b x (α + β) = b3Forms_chartFun b x α + b3Forms_chartFun b x β := by
  funext u
  simp only [b3Forms_chartFun, b3Forms_loc_add, Pi.add_apply]
  by_cases hu : u ∈ (chartAt E x).target <;> simp [hu]

theorem b3Forms_chartFun_smul (x : M) (c : ℝ) (α : M → E [⋀^Fin n]→L[ℝ] ℝ) :
    b3Forms_chartFun b x (c • α) = c • b3Forms_chartFun b x α := by
  funext u
  simp only [b3Forms_chartFun, b3Forms_loc_smul, Pi.smul_apply]
  by_cases hu : u ∈ (chartAt E x).target <;> simp [hu]

/-- The density vanishes off the chart image of the support. -/
theorem b3Forms_support_chartFun_subset (x : M) (α : M → E [⋀^Fin n]→L[ℝ] ℝ) :
    support (b3Forms_chartFun b x α) ⊆ chartAt E x '' ((chartAt E x).source ∩ support α) := by
  intro u hu
  simp only [b3Forms_chartFun, mem_support, indicator_apply_ne_zero] at hu
  obtain ⟨hut, hne⟩ := hu
  refine ⟨(chartAt E x).symm u, ⟨(chartAt E x).map_target hut, ?_⟩, (chartAt E x).right_inv hut⟩
  intro h0
  apply hne
  simp [b3Forms_loc, h0]

variable [T2Space M]

/-- If the support of `α` lies in a compact subset of the chart domain, the density has compact
support inside the chart image. -/
theorem b3Forms_tsupport_chartFun_subset {x : M} {α : M → E [⋀^Fin n]→L[ℝ] ℝ}
    (hc : IsCompact (tsupport α)) (hx : tsupport α ⊆ (chartAt E x).source) :
    tsupport (b3Forms_chartFun b x α) ⊆ chartAt E x '' tsupport α ∧
      IsCompact (chartAt E x '' tsupport α) := by
  have hK : IsCompact (chartAt E x '' tsupport α) :=
    hc.image_of_continuousOn ((chartAt E x).continuousOn.mono hx)
  refine ⟨closure_minimal ?_ hK.isClosed, hK⟩
  refine (b3Forms_support_chartFun_subset b x α).trans (image_mono ?_)
  exact inter_subset_right.trans (subset_tsupport α)

theorem b3Forms_hasCompactSupport_chartFun {x : M} {α : M → E [⋀^Fin n]→L[ℝ] ℝ}
    (hc : IsCompact (tsupport α)) (hx : tsupport α ⊆ (chartAt E x).source) :
    HasCompactSupport (b3Forms_chartFun b x α) :=
  (b3Forms_tsupport_chartFun_subset b hc hx).2.of_isClosed_subset (isClosed_tsupport _)
    (b3Forms_tsupport_chartFun_subset b hc hx).1

/-- The density of a form with continuous local representatives and compact support in the chart
is continuous. -/
theorem b3Forms_continuous_chartFun {x : M} {α : M → E [⋀^Fin n]→L[ℝ] ℝ}
    (hα : ContinuousOn (b3Forms_loc α x) (chartAt E x).target)
    (hc : IsCompact (tsupport α)) (hx : tsupport α ⊆ (chartAt E x).source) :
    Continuous (b3Forms_chartFun b x α) := by
  obtain ⟨hsub, hK⟩ := b3Forms_tsupport_chartFun_subset b hc hx
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u ∈ (chartAt E x).target
  · have hO := (chartAt E x).open_target.mem_nhds hu
    have hcont : ContinuousAt (fun u ↦ b3Forms_loc α x u b) u :=
      (continuous_eval_const _).continuousAt.comp ((hα.continuousAt hO))
    refine hcont.congr ?_
    filter_upwards [hO] with v hv
    simp [b3Forms_chartFun, hv]
  · have hKt : chartAt E x '' tsupport α ⊆ (chartAt E x).target := by
      rintro _ ⟨z, hz, rfl⟩
      exact (chartAt E x).map_source (hx hz)
    have hO : (chartAt E x '' tsupport α)ᶜ ∈ 𝓝 u :=
      hK.isClosed.isOpen_compl.mem_nhds fun h ↦ hu (hKt h)
    refine continuousAt_const.congr (f := fun _ ↦ (0 : ℝ)) ?_
    filter_upwards [hO] with v hv
    exact (image_eq_zero_of_notMem_tsupport fun h ↦ hv (hsub h)).symm

end Chart

section ChartIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ E)

/-- **The integral of an `n`-form in the chart at `x`.**
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_chartIntegral (x : M) (α : M → E [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  ∫ u, b3Forms_chartFun b x α u ∂b.addHaar

/-- **An oriented atlas**: every change of coordinates has positive Jacobian determinant. -/
def b3Forms_Oriented (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  ∀ (x y : M) (u : E), u ∈ b3Forms_trDom x y →
    0 < LinearMap.det (fderiv ℝ (b3Forms_tr x y) u : E →ₗ[ℝ] E)

theorem b3Forms_image_trDom (x y : M) :
    b3Forms_tr (E := E) x y '' b3Forms_trDom x y = b3Forms_trDom y x := by
  have h := ((chartAt E x).symm ≫ₕ chartAt E y).image_source_eq_target
  rw [← b3Forms_trDom_eq] at h
  rw [show b3Forms_tr (E := E) x y = ((chartAt E x).symm ≫ₕ chartAt E y) from rfl, h,
    OpenPartialHomeomorph.trans_target]
  rfl

theorem b3Forms_chartFun_eq_zero_of_notMem {x y : M} {α : M → E [⋀^Fin n]→L[ℝ] ℝ}
    (hy : tsupport α ⊆ (chartAt E y).source) {u : E} (hu : u ∉ b3Forms_trDom x y) :
    b3Forms_chartFun b x α u = 0 := by
  by_contra h
  obtain ⟨z, ⟨hzx, hz⟩, rfl⟩ := b3Forms_support_chartFun_subset b x α h
  apply hu
  refine ⟨(chartAt E x).map_source hzx, ?_⟩
  rw [mem_preimage, (chartAt E x).left_inv hzx]
  exact hy (subset_tsupport α hz)

variable [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **Independence of the chart**: for a form supported in a compact subset of two chart
domains, the two chart integrals agree when the change of coordinates is orientation
preserving. -/
theorem b3Forms_chartIntegral_eq_of_tsupport_subset (hor : b3Forms_Oriented E M)
    {α : M → E [⋀^Fin n]→L[ℝ] ℝ} {x y : M}
    (hx : tsupport α ⊆ (chartAt E x).source) (hy : tsupport α ⊆ (chartAt E y).source) :
    b3Forms_chartIntegral b x α = b3Forms_chartIntegral b y α := by
  have hs : MeasurableSet (b3Forms_trDom (E := E) x y) :=
    (b3Forms_isOpen_trDom x y).measurableSet
  have h1 : b3Forms_chartIntegral b x α =
      ∫ u in b3Forms_trDom x y, b3Forms_chartFun b x α u ∂b.addHaar :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      fun u hu ↦ b3Forms_chartFun_eq_zero_of_notMem b hy hu).symm
  have h2 : b3Forms_chartIntegral b y α =
      ∫ u in b3Forms_trDom y x, b3Forms_chartFun b y α u ∂b.addHaar :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      fun u hu ↦ b3Forms_chartFun_eq_zero_of_notMem b hx hu).symm
  rw [h1, h2, ← b3Forms_image_trDom x y,
    integral_image_eq_integral_abs_det_fderiv_smul b.addHaar hs
      (fun u hu ↦ (b3Forms_differentiableAt_tr hu).hasFDerivAt.hasFDerivWithinAt)
      ((chartAt E y).injOn.comp ((chartAt E x).symm.injOn.mono inter_subset_left)
        (fun u hu ↦ hu.2))]
  refine setIntegral_congr_fun hs fun u hu ↦ ?_
  simp only [b3Forms_chartFun, indicator_of_mem hu.1,
    indicator_of_mem (b3Forms_tr_mem_target hu), smul_eq_mul]
  rw [b3Forms_loc_eq_comp α hu, b3Forms_comp_apply_basis, abs_of_pos (hor x y u hu)]

/-- The density of a smooth form compactly supported in the chart domain is integrable. -/
theorem b3Forms_integrable_chartFun {α : M → E [⋀^Fin n]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hc : IsCompact (tsupport α)) {x : M} (hx : tsupport α ⊆ (chartAt E x).source) :
    Integrable (b3Forms_chartFun b x α) b.addHaar :=
  (b3Forms_continuous_chartFun b (hα x).continuousOn hc hx).integrable_of_hasCompactSupport
    (b3Forms_hasCompactSupport_chartFun b hc hx)

/-- The density in a chart as a linear map.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_chartFunL (x : M) : (M → E [⋀^Fin n]→L[ℝ] ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := b3Forms_chartFun b x
  map_add' := b3Forms_chartFun_add b x
  map_smul' c α := b3Forms_chartFun_smul b x c α

theorem b3Forms_chartIntegral_add (hc : ∀ γ : M → E [⋀^Fin n]→L[ℝ] ℝ, IsCompact (tsupport γ))
    {α β : M → E [⋀^Fin n]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (hβ : b3Forms_IsSmooth β) {x : M}
    (hαx : tsupport α ⊆ (chartAt E x).source) (hβx : tsupport β ⊆ (chartAt E x).source) :
    b3Forms_chartIntegral b x (α + β) =
      b3Forms_chartIntegral b x α + b3Forms_chartIntegral b x β := by
  simp only [b3Forms_chartIntegral, b3Forms_chartFun_add]
  exact integral_add (b3Forms_integrable_chartFun b hα (hc α) hαx)
    (b3Forms_integrable_chartFun b hβ (hc β) hβx)

theorem b3Forms_chartIntegral_smul (x : M) (c : ℝ) (α : M → E [⋀^Fin n]→L[ℝ] ℝ) :
    b3Forms_chartIntegral b x (c • α) = c * b3Forms_chartIntegral b x α := by
  simp only [b3Forms_chartIntegral, b3Forms_chartFun_smul, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem b3Forms_chartIntegral_finsetSum
    (hc : ∀ γ : M → E [⋀^Fin n]→L[ℝ] ℝ, IsCompact (tsupport γ)) {ι : Type*} (S : Finset ι)
    {α : ι → M → E [⋀^Fin n]→L[ℝ] ℝ} (hα : ∀ i ∈ S, b3Forms_IsSmooth (α i)) {x : M}
    (hαx : ∀ i ∈ S, tsupport (α i) ⊆ (chartAt E x).source) :
    b3Forms_chartIntegral b x (∑ i ∈ S, α i) = ∑ i ∈ S, b3Forms_chartIntegral b x (α i) := by
  simp only [b3Forms_chartIntegral]
  rw [show b3Forms_chartFun b x (∑ i ∈ S, α i) = ∑ i ∈ S, b3Forms_chartFun b x (α i) from
    map_sum (b3Forms_chartFunL b x) α S]
  simp only [Finset.sum_apply]
  exact integral_finsetSum S fun i hi ↦ b3Forms_integrable_chartFun b (hα i hi) (hc _) (hαx i hi)

end ChartIntegral

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ E)

variable (E M) in
/-- A smooth partition of unity subordinate to the chart domains, indexed by the chart centres.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_pou : SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, E) M).choose

theorem b3Forms_pou_isSubordinate :
    (b3Forms_pou E M).IsSubordinate fun x ↦ (chartAt E x).source :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, E) M).choose_spec

/-- **The integral of an `n`-form** over a compact manifold, `∑ᶠ i, ∫_{chart i} ρᵢ α`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_integral (α : M → E [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  ∑ᶠ i, b3Forms_chartIntegral b i (b3Forms_smulFun (b3Forms_pou E M i) α)

theorem b3Forms_isCompact_tsupport (γ : M → E [⋀^Fin n]→L[ℝ] ℝ) : IsCompact (tsupport γ) :=
  (isClosed_tsupport γ).isCompact

theorem b3Forms_tsupport_smulFun_subset_left {k : ℕ} (g : M → ℝ)
    (α : M → E [⋀^Fin k]→L[ℝ] ℝ) : tsupport (b3Forms_smulFun g α) ⊆ tsupport g :=
  tsupport_smul_subset_left g α

theorem b3Forms_tsupport_smulFun_subset_right {k : ℕ} (g : M → ℝ)
    (α : M → E [⋀^Fin k]→L[ℝ] ℝ) : tsupport (b3Forms_smulFun g α) ⊆ tsupport α :=
  tsupport_smul_subset_right g α

/-- The finitely many indices of the partition of unity with nonzero function.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_pouSupp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] : Finset M :=
  ((b3Forms_pou E M).locallyFinite.finite_nonempty_of_compact).toFinset

theorem b3Forms_pou_eq_zero {i : M} (hi : i ∉ b3Forms_pouSupp E M) :
    ⇑(b3Forms_pou E M i) = 0 := by
  funext z
  by_contra h
  exact hi ((Set.Finite.mem_toFinset _).2 ⟨z, h⟩)

theorem b3Forms_sum_pou (z : M) : ∑ i ∈ b3Forms_pouSupp E M, b3Forms_pou E M i z = 1 := by
  rw [← (b3Forms_pou E M).sum_eq_one (mem_univ z)]
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).symm
  by_contra h
  exact hi (congrFun (b3Forms_pou_eq_zero h) z)

theorem b3Forms_sum_smulFun_pou {k : ℕ} (α : M → E [⋀^Fin k]→L[ℝ] ℝ) :
    ∑ i ∈ b3Forms_pouSupp E M, b3Forms_smulFun (b3Forms_pou E M i) α = α := by
  funext z
  simp only [Finset.sum_apply, b3Forms_smulFun, ← Finset.sum_smul, b3Forms_sum_pou, one_smul]

theorem b3Forms_integral_eq_sum (α : M → E [⋀^Fin n]→L[ℝ] ℝ) :
    b3Forms_integral b α = ∑ i ∈ b3Forms_pouSupp E M,
      b3Forms_chartIntegral b i (b3Forms_smulFun (b3Forms_pou E M i) α) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  by_contra h
  apply hi
  simp [b3Forms_smulFun, b3Forms_pou_eq_zero h, b3Forms_chartIntegral, b3Forms_chartFun,
    b3Forms_loc]

theorem b3Forms_IsSmooth.smulFun_pou {k : ℕ} {α : M → E [⋀^Fin k]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (i : M) :
    b3Forms_IsSmooth (b3Forms_smulFun (b3Forms_pou E M i) α) :=
  hα.smulFun (b3Forms_pou E M i).contMDiff

/-- **The integral of a form supported in one chart is its chart integral.** -/
theorem b3Forms_integral_eq_chartIntegral (hor : b3Forms_Oriented E M)
    {α : M → E [⋀^Fin n]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) {x : M}
    (hx : tsupport α ⊆ (chartAt E x).source) :
    b3Forms_integral b α = b3Forms_chartIntegral b x α := by
  rw [b3Forms_integral_eq_sum]
  have h1 : ∀ i ∈ b3Forms_pouSupp E M,
      b3Forms_chartIntegral b i (b3Forms_smulFun (b3Forms_pou E M i) α) =
        b3Forms_chartIntegral b x (b3Forms_smulFun (b3Forms_pou E M i) α) := fun i _ ↦
    b3Forms_chartIntegral_eq_of_tsupport_subset b hor
      ((b3Forms_tsupport_smulFun_subset_left _ _).trans (b3Forms_pou_isSubordinate i))
      ((b3Forms_tsupport_smulFun_subset_right _ _).trans hx)
  rw [Finset.sum_congr rfl h1, ← b3Forms_chartIntegral_finsetSum b b3Forms_isCompact_tsupport _
    (fun i _ ↦ hα.smulFun_pou i) (fun i _ ↦ (b3Forms_tsupport_smulFun_subset_right _ _).trans hx),
    b3Forms_sum_smulFun_pou]

theorem b3Forms_integral_add {α β : M → E [⋀^Fin n]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hβ : b3Forms_IsSmooth β) :
    b3Forms_integral b (α + β) = b3Forms_integral b α + b3Forms_integral b β := by
  simp only [b3Forms_integral_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsub := fun γ : M → E [⋀^Fin n]→L[ℝ] ℝ ↦
    (b3Forms_tsupport_smulFun_subset_left (b3Forms_pou E M i) γ).trans
      (b3Forms_pou_isSubordinate i)
  rw [show b3Forms_smulFun (b3Forms_pou E M i) (α + β) =
      b3Forms_smulFun (b3Forms_pou E M i) α + b3Forms_smulFun (b3Forms_pou E M i) β by
    funext z; simp [b3Forms_smulFun]]
  exact b3Forms_chartIntegral_add b b3Forms_isCompact_tsupport (hα.smulFun_pou i)
    (hβ.smulFun_pou i) (hsub α) (hsub β)

theorem b3Forms_integral_smul (c : ℝ) (α : M → E [⋀^Fin n]→L[ℝ] ℝ) :
    b3Forms_integral b (c • α) = c * b3Forms_integral b α := by
  simp only [b3Forms_integral_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show b3Forms_smulFun (b3Forms_pou E M i) (c • α) =
      c • b3Forms_smulFun (b3Forms_pou E M i) α by
    funext z; simp [b3Forms_smulFun, smul_comm c]]
  exact b3Forms_chartIntegral_smul b i c _

theorem b3Forms_integral_finsetSum {ι : Type*} (S : Finset ι) {α : ι → M → E [⋀^Fin n]→L[ℝ] ℝ}
    (hα : ∀ i ∈ S, b3Forms_IsSmooth (α i)) :
    b3Forms_integral b (∑ i ∈ S, α i) = ∑ i ∈ S, b3Forms_integral b (α i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using b3Forms_integral_smul b 0 (0 : M → E [⋀^Fin n]→L[ℝ] ℝ)
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, b3Forms_integral_add b
      (hα j (Finset.mem_insert_self j S)), ih fun i hi ↦ hα i (Finset.mem_insert_of_mem hi)]
    have : ∀ i ∈ S, b3Forms_IsSmooth (α i) := fun i hi ↦ hα i (Finset.mem_insert_of_mem hi)
    exact (b3Forms_Ω E M n).sum_mem this

/-- **The integral as a linear functional** on smooth `n`-forms.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 16 (integration of forms,
Stokes' theorem); Mathlib `SmoothPartitionOfUnity`. -/
def b3Forms_integralL : b3Forms_Ω E M n →ₗ[ℝ] ℝ where
  toFun α := b3Forms_integral b α.1
  map_add' α β := b3Forms_integral_add b α.2 β.2
  map_smul' c α := b3Forms_integral_smul b c α.1

/-- **Independence of the partition of unity**: any smooth partition of unity subordinate to
chart domains computes the same integral. -/
theorem b3Forms_integral_eq_of_pou (hor : b3Forms_Oriented E M) {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M univ) (c : ι → M)
    (hρ : ρ.IsSubordinate fun i ↦ (chartAt E (c i)).source)
    {α : M → E [⋀^Fin n]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) :
    ∑ᶠ i, b3Forms_chartIntegral b (c i) (b3Forms_smulFun (ρ i) α) = b3Forms_integral b α := by
  have hfin := ρ.locallyFinite.finite_nonempty_of_compact
  have hz : ∀ i ∉ hfin.toFinset, ⇑(ρ i) = 0 := fun i hi ↦ by
    funext z
    by_contra h
    exact hi ((Set.Finite.mem_toFinset _).2 ⟨z, h⟩)
  have hsm : ∀ i, b3Forms_IsSmooth (b3Forms_smulFun (ρ i) α) := fun i ↦ hα.smulFun (ρ i).contMDiff
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun i hi ↦ ?_]
  · rw [Finset.sum_congr rfl fun i _ ↦ (b3Forms_integral_eq_chartIntegral b hor (hsm i)
      ((b3Forms_tsupport_smulFun_subset_left _ _).trans (hρ i))).symm,
      ← b3Forms_integral_finsetSum b _ fun i _ ↦ hsm i]
    congr 1
    funext z
    simp only [Finset.sum_apply, b3Forms_smulFun, ← Finset.sum_smul]
    rw [show ∑ i ∈ hfin.toFinset, ρ i z = 1 from ?_, one_smul]
    rw [← ρ.sum_eq_one (mem_univ z)]
    refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).symm
    by_contra h
    exact hi (congrFun (hz i h) z)
  · by_contra h
    apply hi
    simp [b3Forms_smulFun, hz i h, b3Forms_chartIntegral, b3Forms_chartFun, b3Forms_loc]

theorem b3Forms_chartFun_smulFun_pou (α : M → E [⋀^Fin n]→L[ℝ] ℝ) (i : M) {u : E}
    (hu : u ∈ (chartAt E i).target) :
    b3Forms_chartFun b i (b3Forms_smulFun (b3Forms_pou E M i) α) u =
      b3Forms_pou E M i ((chartAt E i).symm u) * b3Forms_loc α i u b := by
  simp only [b3Forms_chartFun, indicator_of_mem hu, b3Forms_loc_smulFun,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- **A form with nonnegative densities has nonnegative integral.** -/
theorem b3Forms_integral_nonneg {α : M → E [⋀^Fin n]→L[ℝ] ℝ}
    (hnn : ∀ (x : M) (u : E), u ∈ (chartAt E x).target → 0 ≤ b3Forms_loc α x u b) :
    0 ≤ b3Forms_integral b α := by
  rw [b3Forms_integral_eq_sum]
  refine Finset.sum_nonneg fun i _ ↦ MeasureTheory.integral_nonneg fun u ↦ ?_
  by_cases hu : u ∈ (chartAt E i).target
  · rw [b3Forms_chartFun_smulFun_pou b α i hu]
    exact mul_nonneg ((b3Forms_pou E M).nonneg i _) (hnn i u hu)
  · simp [b3Forms_chartFun, hu]

/-- **A smooth form with nonnegative densities, positive at one point, has positive
integral.** -/
theorem b3Forms_integral_pos {α : M → E [⋀^Fin n]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hnn : ∀ (x : M) (u : E), u ∈ (chartAt E x).target → 0 ≤ b3Forms_loc α x u b) (z₀ : M)
    (hpos : ∀ x : M, z₀ ∈ (chartAt E x).source → 0 < b3Forms_loc α x (chartAt E x z₀) b) :
    0 < b3Forms_integral b α := by
  have hnn' : ∀ i : M, 0 ≤ b3Forms_chartFun b i (b3Forms_smulFun (b3Forms_pou E M i) α) :=
    fun i u ↦ by
      by_cases hu : u ∈ (chartAt E i).target
      · rw [b3Forms_chartFun_smulFun_pou b α i hu]
        exact mul_nonneg ((b3Forms_pou E M).nonneg i _) (hnn i u hu)
      · simp [b3Forms_chartFun, hu]
  rw [b3Forms_integral_eq_sum]
  obtain ⟨i, hi⟩ := (b3Forms_pou E M).exists_pos_of_mem (mem_univ z₀)
  have hiS : i ∈ b3Forms_pouSupp E M := (Set.Finite.mem_toFinset _).2 ⟨z₀, hi.ne'⟩
  refine Finset.sum_pos' (fun j _ ↦ MeasureTheory.integral_nonneg (hnn' j)) ⟨i, hiS, ?_⟩
  have hsrc : z₀ ∈ (chartAt E i).source :=
    b3Forms_pou_isSubordinate i (subset_tsupport _ hi.ne')
  set u₀ := chartAt E i z₀
  have hu₀ : u₀ ∈ (chartAt E i).target := (chartAt E i).map_source hsrc
  have hsm := hα.smulFun_pou i
  have hsub : tsupport (b3Forms_smulFun (b3Forms_pou E M i) α) ⊆ (chartAt E i).source :=
    (b3Forms_tsupport_smulFun_subset_left _ _).trans (b3Forms_pou_isSubordinate i)
  have hcont := b3Forms_continuous_chartFun b (hsm i).continuousOn
    (b3Forms_isCompact_tsupport _) hsub
  have hint := b3Forms_integrable_chartFun b hsm (b3Forms_isCompact_tsupport _) hsub
  have hp : 0 < b3Forms_chartFun b i (b3Forms_smulFun (b3Forms_pou E M i) α) u₀ := by
    rw [b3Forms_chartFun_smulFun_pou b α i hu₀, (chartAt E i).left_inv hsrc]
    exact mul_pos hi (hpos i hsrc)
  rw [b3Forms_chartIntegral, MeasureTheory.integral_pos_iff_support_of_nonneg (hnn' i) hint]
  exact lt_of_lt_of_le ((isOpen_lt continuous_const hcont).measure_pos b.addHaar ⟨u₀, hp⟩)
    (MeasureTheory.measure_mono fun u hu ↦ ne_of_gt hu)

end Integral

end HodgeLean.Foundations.Program
