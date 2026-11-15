import Mathlib

/-!
# Track B3 foundations (stage B3.4a): smooth differential forms on manifolds

Mathlib has the exterior derivative `extDeriv` of forms `E → E [⋀^Fin k]→L[ℝ] F` on a normed space,
with `d ∘ d = 0` and naturality under pullback, but no forms on manifolds. This file builds them on
a boundaryless manifold `M` modelled on a real normed space `E` (`ChartedSpace E M`,
`IsManifold 𝓘(ℝ, E) ∞ M`), which covers a Riemann surface read as a real surface.

A `k`-form is a family `α : M → E [⋀^Fin k]→L[ℝ] ℝ`, the value `α z` being read in the
coordinates of the chart at `z` (Mathlib's convention for `TangentSpace 𝓘(ℝ, E) z = E`).
* `b3Forms_tr x y`, the change of coordinates, and its chain rule `b3Forms_fderiv_tr_comp`;
* `b3Forms_loc α x`, the local representative in the chart at `x`, and the cocycle condition
  `b3Forms_loc_eq_comp` relating two charts;
* `b3Forms_IsSmooth`, `b3Forms_Ω E M k` (smooth `k`-forms), the exterior derivative
  `b3Forms_d` / `b3Forms_dL`, its chart formula `b3Forms_loc_d` and `b3Forms_d_d`;
* closed and exact forms and the de Rham groups `b3Forms_deRham E M k = Hᵏ⁺¹_dR(M)`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Linear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- A function into a finite-dimensional space is smooth when its composite with an injective
linear map to another finite-dimensional space is. -/
theorem b3Forms_contDiffOn_of_injective {n : WithTop ℕ∞} (L : F →L[ℝ] G)
    (hL : Function.Injective L) {f : E → F} {s : Set E}
    (hf : ContDiffOn ℝ n (fun x ↦ L (f x)) s) : ContDiffOn ℝ n f s := by
  obtain ⟨g, hg⟩ := (L : F →ₗ[ℝ] G).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hL)
  have : f = fun x ↦ LinearMap.toContinuousLinearMap g (L (f x)) := by
    funext x
    exact (LinearMap.congr_fun hg (f x)).symm
  rw [this]
  exact (LinearMap.toContinuousLinearMap g).contDiff.comp_contDiffOn hf

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']

/-- Continuous multilinear forms on a finite-dimensional space form a finite-dimensional space. -/
instance b3Forms_finiteDimensional_multilinear {ι : Type*} [Fintype ι] :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : ι ↦ F') ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- The pullback `(g, A) ↦ g ∘ A` of alternating maps along linear maps is smooth in both
arguments. -/
theorem b3Forms_contDiffOn_comp {k : ℕ} {n : WithTop ℕ∞} {g : E → F [⋀^Fin k]→L[ℝ] ℝ}
    {A : E → F' →L[ℝ] F} {s : Set E} (hg : ContDiffOn ℝ n g s) (hA : ContDiffOn ℝ n A s) :
    ContDiffOn ℝ n (fun u ↦ (g u).compContinuousLinearMap (A u)) s := by
  refine b3Forms_contDiffOn_of_injective (toContinuousMultilinearMapCLM ℝ)
    toContinuousMultilinearMap_injective ?_
  have h1 : ContDiffOn ℝ n (fun u ↦ toContinuousMultilinearMapCLM ℝ (g u)) s :=
    ((toContinuousMultilinearMapCLM ℝ).contDiff.comp_contDiffOn hg :)
  have h2 : ContDiffOn ℝ n (fun u ↦
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k ↦ F') (fun _ : Fin k ↦ F) ℝ (fun _ ↦ A u)) s :=
    (ContinuousMultilinearMap.contDiff _).comp_contDiffOn (contDiffOn_pi.2 fun _ ↦ hA)
  convert h2.clm_apply h1 using 1
  funext u
  rfl

end Linear

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The change of coordinates from the chart at `x` to the chart at `y`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_tr (x y : M) : E → E := chartAt E y ∘ (chartAt E x).symm

/-- The domain of `b3Forms_tr x y`: the chart image at `x` of the overlap of the two charts. -/
def b3Forms_trDom (x y : M) : Set E :=
  (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' (chartAt E y).source

theorem b3Forms_isOpen_trDom (x y : M) : IsOpen (b3Forms_trDom (E := E) x y) :=
  (chartAt E x).isOpen_inter_preimage_symm (chartAt E y).open_source

theorem b3Forms_trDom_eq (x y : M) :
    b3Forms_trDom (E := E) x y = ((chartAt E x).symm ≫ₕ chartAt E y).source := by
  simp [b3Forms_trDom]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem b3Forms_contDiffOn_tr (x y : M) :
    ContDiffOn ℝ ∞ (b3Forms_tr (E := E) x y) (b3Forms_trDom x y) := by
  have := contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (n := ∞) y x
  simpa [b3Forms_tr, b3Forms_trDom, extChartAt, PartialEquiv.trans_source, Function.comp_def]
    using this

theorem b3Forms_mem_trDom {x y : M} {u : E} (hu : u ∈ (chartAt E x).target)
    (hy : (chartAt E x).symm u ∈ (chartAt E y).source) : u ∈ b3Forms_trDom x y := ⟨hu, hy⟩

theorem b3Forms_mem_trDom_self {x : M} {u : E} (hu : u ∈ (chartAt E x).target) :
    u ∈ b3Forms_trDom x ((chartAt E x).symm u) := ⟨hu, mem_chart_source E _⟩

theorem b3Forms_contDiffAt_tr {x y : M} {u : E} (hu : u ∈ b3Forms_trDom x y) :
    ContDiffAt ℝ ∞ (b3Forms_tr (E := E) x y) u :=
  (b3Forms_contDiffOn_tr x y).contDiffAt ((b3Forms_isOpen_trDom x y).mem_nhds hu)

theorem b3Forms_differentiableAt_tr {x y : M} {u : E} (hu : u ∈ b3Forms_trDom x y) :
    DifferentiableAt ℝ (b3Forms_tr (E := E) x y) u :=
  (b3Forms_contDiffAt_tr hu).differentiableAt (by simp)

theorem b3Forms_tr_mem_target {x y : M} {u : E} (hu : u ∈ b3Forms_trDom x y) :
    b3Forms_tr (E := E) x y u ∈ (chartAt E y).target :=
  (chartAt E y).map_source hu.2

theorem b3Forms_symm_tr {x y : M} {u : E} (hu : u ∈ b3Forms_trDom x y) :
    (chartAt E y).symm (b3Forms_tr (E := E) x y u) = (chartAt E x).symm u :=
  (chartAt E y).left_inv hu.2

/-- The chain rule for changes of coordinates: near a point of the triple overlap,
`tr y z ∘ tr x y = tr x z`. -/
theorem b3Forms_tr_comp_eventuallyEq {x y z : M} {u : E} (hu : u ∈ b3Forms_trDom x y) :
    b3Forms_tr (E := E) y z ∘ b3Forms_tr x y =ᶠ[𝓝 u] b3Forms_tr x z := by
  filter_upwards [(b3Forms_isOpen_trDom x y).mem_nhds hu] with v hv
  simp only [Function.comp_apply, b3Forms_tr]
  rw [(chartAt E y).left_inv hv.2]

/-- The derivative of a change of coordinates factors through an intermediate chart. -/
theorem b3Forms_fderiv_tr_comp {x y z : M} {u : E} (hu : u ∈ b3Forms_trDom x y)
    (hz : (chartAt E x).symm u ∈ (chartAt E z).source) :
    fderiv ℝ (b3Forms_tr (E := E) x z) u =
      (fderiv ℝ (b3Forms_tr y z) (b3Forms_tr x y u)).comp (fderiv ℝ (b3Forms_tr x y) u) := by
  rw [← (b3Forms_tr_comp_eventuallyEq (z := z) hu).fderiv_eq]
  refine fderiv_comp _ (b3Forms_differentiableAt_tr ?_) (b3Forms_differentiableAt_tr hu)
  exact ⟨b3Forms_tr_mem_target hu, by rw [mem_preimage, b3Forms_symm_tr hu]; exact hz⟩

/-- The change of coordinates from a chart to itself is the identity near each point. -/
theorem b3Forms_tr_self_eventuallyEq {x : M} {u : E} (hu : u ∈ (chartAt E x).target) :
    b3Forms_tr (E := E) x x =ᶠ[𝓝 u] id := by
  filter_upwards [(chartAt E x).open_target.mem_nhds hu] with v hv
  exact (chartAt E x).right_inv hv

theorem b3Forms_fderiv_tr_self {x : M} {u : E} (hu : u ∈ (chartAt E x).target) :
    fderiv ℝ (b3Forms_tr (E := E) x x) u = ContinuousLinearMap.id ℝ E := by
  rw [(b3Forms_tr_self_eventuallyEq hu).fderiv_eq, fderiv_id]

end Charts

section Forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {k : ℕ}

/-- **The local representative** of a family `α` of alternating `k`-forms on the tangent spaces of
`M` in the chart at `x`. The value `α z` is read in the coordinates of the chart at `z`; at the
point `u` of the chart at `x` it is pulled back to the coordinates of the chart at `x` along the
derivative of the change of coordinates.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_loc (α : M → E [⋀^Fin k]→L[ℝ] ℝ) (x : M) (u : E) : E [⋀^Fin k]→L[ℝ] ℝ :=
  (α ((chartAt E x).symm u)).compContinuousLinearMap
    (fderiv ℝ (b3Forms_tr x ((chartAt E x).symm u)) u)

theorem b3Forms_loc_add (α β : M → E [⋀^Fin k]→L[ℝ] ℝ) (x : M) :
    b3Forms_loc (α + β) x = b3Forms_loc α x + b3Forms_loc β x := by
  funext u
  ext v
  simp [b3Forms_loc]

theorem b3Forms_loc_smul (c : ℝ) (α : M → E [⋀^Fin k]→L[ℝ] ℝ) (x : M) :
    b3Forms_loc (c • α) x = c • b3Forms_loc α x := by
  funext u
  ext v
  simp [b3Forms_loc]

theorem b3Forms_loc_zero (x : M) :
    b3Forms_loc (0 : M → E [⋀^Fin k]→L[ℝ] ℝ) x = 0 := by
  funext u
  ext v
  simp [b3Forms_loc]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The cocycle condition**: on the overlap of two charts the local representatives are related
by the pullback along the change of coordinates. -/
theorem b3Forms_loc_eq_comp (α : M → E [⋀^Fin k]→L[ℝ] ℝ) {x y : M} {u : E}
    (hu : u ∈ b3Forms_trDom x y) :
    b3Forms_loc α x u = (b3Forms_loc α y (b3Forms_tr x y u)).compContinuousLinearMap
      (fderiv ℝ (b3Forms_tr x y) u) := by
  simp only [b3Forms_loc, b3Forms_symm_tr hu]
  rw [b3Forms_fderiv_tr_comp hu (mem_chart_source E _)]
  ext v
  simp [Function.comp_def]

/-- The value of a family of forms is its local representative at the centre of the chart. -/
theorem b3Forms_loc_self (α : M → E [⋀^Fin k]→L[ℝ] ℝ) (x : M) :
    b3Forms_loc α x (chartAt E x x) = α x := by
  have hx : (chartAt E x).symm (chartAt E x x) = x := (chartAt E x).left_inv (mem_chart_source E x)
  simp only [b3Forms_loc, hx]
  rw [b3Forms_fderiv_tr_self ((chartAt E x).map_source (mem_chart_source E x))]
  ext v
  simp

/-- The local representative in another chart, at a point of the overlap. -/
theorem b3Forms_loc_chart (α : M → E [⋀^Fin k]→L[ℝ] ℝ) {x z : M}
    (hz : z ∈ (chartAt E x).source) :
    b3Forms_loc α x (chartAt E x z) =
      (α z).compContinuousLinearMap (fderiv ℝ (b3Forms_tr x z) (chartAt E x z)) := by
  simp only [b3Forms_loc, (chartAt E x).left_inv hz]

/-- **Smooth `k`-forms**: every local representative is smooth on its chart.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_IsSmooth (α : M → E [⋀^Fin k]→L[ℝ] ℝ) : Prop :=
  ∀ x : M, ContDiffOn ℝ ∞ (b3Forms_loc α x) (chartAt E x).target

/-- **The smooth `k`-forms** `Ωᵏ(M)` as a real vector space. -/
def b3Forms_Ω (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (k : ℕ) :
    Submodule ℝ (M → E [⋀^Fin k]→L[ℝ] ℝ) where
  carrier := {α | b3Forms_IsSmooth α}
  add_mem' {α β} hα hβ x := by
    rw [b3Forms_loc_add]
    exact (hα x).add (hβ x)
  zero_mem' x := by
    rw [b3Forms_loc_zero]
    exact contDiffOn_const
  smul_mem' c α hα x := by
    rw [b3Forms_loc_smul]
    exact (hα x).const_smul c

theorem b3Forms_IsSmooth.add {α β : M → E [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hβ : b3Forms_IsSmooth β) : b3Forms_IsSmooth (α + β) :=
  (b3Forms_Ω E M k).add_mem hα hβ

theorem b3Forms_IsSmooth.smul (c : ℝ) {α : M → E [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) :
    b3Forms_IsSmooth (c • α) :=
  (b3Forms_Ω E M k).smul_mem c hα

theorem b3Forms_minSmoothness_le : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.2 le_top

theorem b3Forms_IsSmooth.contDiffAt {α : M → E [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    {x : M} {u : E} (hu : u ∈ (chartAt E x).target) :
    ContDiffAt ℝ ∞ (b3Forms_loc α x) u :=
  (hα x).contDiffAt ((chartAt E x).open_target.mem_nhds hu)

/-- **The exterior derivative** of a family of `k`-forms: at `z`, Mathlib's `extDeriv` of the
local representative in the chart at `z`, at the centre of that chart.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_d (α : M → E [⋀^Fin k]→L[ℝ] ℝ) : M → E [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  fun z ↦ extDeriv (b3Forms_loc α z) (chartAt E z z)

/-- **The exterior derivative in a chart**: the local representative of `dα` is the exterior
derivative of the local representative of `α`. -/
theorem b3Forms_loc_d {α : M → E [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (x : M) :
    EqOn (b3Forms_loc (b3Forms_d α) x) (extDeriv (b3Forms_loc α x)) (chartAt E x).target := by
  intro u hu
  set z := (chartAt E x).symm u
  have hu' : u ∈ b3Forms_trDom x z := b3Forms_mem_trDom_self hu
  have hloc : b3Forms_loc α x =ᶠ[𝓝 u] fun u' ↦
      (b3Forms_loc α z (b3Forms_tr x z u')).compContinuousLinearMap
        (fderiv ℝ (b3Forms_tr x z) u') := by
    filter_upwards [(b3Forms_isOpen_trDom x z).mem_nhds hu'] with v hv
    exact b3Forms_loc_eq_comp α hv
  rw [hloc.extDeriv_eq, extDeriv_pullback (r := ∞) _ (b3Forms_contDiffAt_tr hu')
    b3Forms_minSmoothness_le]
  · rfl
  · exact (hα.contDiffAt (b3Forms_tr_mem_target hu')).differentiableAt (by simp)

theorem b3Forms_contDiffOn_extDeriv {f : E → E [⋀^Fin k]→L[ℝ] ℝ} {s : Set E}
    (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s) : ContDiffOn ℝ ∞ (extDeriv f) s :=
  (alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp_contDiffOn
    (hf.fderiv_of_isOpen hs (by simp))

/-- The exterior derivative of a smooth form is smooth. -/
theorem b3Forms_IsSmooth.d {α : M → E [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) :
    b3Forms_IsSmooth (b3Forms_d α) := fun x ↦
  ((b3Forms_contDiffOn_extDeriv (hα x) (chartAt E x).open_target)).congr (b3Forms_loc_d hα x)

/-- **`d ∘ d = 0`** on smooth forms. -/
theorem b3Forms_d_d {α : M → E [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) :
    b3Forms_d (b3Forms_d α) = 0 := by
  funext z
  have hz := (chartAt E z).map_source (mem_chart_source E z)
  have h : b3Forms_loc (b3Forms_d α) z =ᶠ[𝓝 (chartAt E z z)] extDeriv (b3Forms_loc α z) := by
    filter_upwards [(chartAt E z).open_target.mem_nhds hz] with v hv
    exact b3Forms_loc_d hα z hv
  show extDeriv _ _ = 0
  rw [h.extDeriv_eq]
  exact extDeriv_extDeriv_apply (hα.contDiffAt hz) b3Forms_minSmoothness_le

theorem b3Forms_d_add {α β : M → E [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hβ : b3Forms_IsSmooth β) : b3Forms_d (α + β) = b3Forms_d α + b3Forms_d β := by
  funext z
  have hz := (chartAt E z).map_source (mem_chart_source E z)
  simp only [b3Forms_d, b3Forms_loc_add, Pi.add_apply]
  exact extDeriv_add ((hα.contDiffAt hz).differentiableAt (by simp))
    ((hβ.contDiffAt hz).differentiableAt (by simp))

theorem b3Forms_d_smul (c : ℝ) (α : M → E [⋀^Fin k]→L[ℝ] ℝ) :
    b3Forms_d (c • α) = c • b3Forms_d α := by
  funext z
  simp only [b3Forms_d, b3Forms_loc_smul, Pi.smul_apply]
  exact extDeriv_smul c _

/-- **The exterior derivative** `d : Ωᵏ(M) → Ωᵏ⁺¹(M)` as a linear map.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_dL : b3Forms_Ω E M k →ₗ[ℝ] b3Forms_Ω E M (k + 1) where
  toFun α := ⟨b3Forms_d α.1, α.2.d⟩
  map_add' α β := Subtype.ext (b3Forms_d_add α.2 β.2)
  map_smul' c α := Subtype.ext (b3Forms_d_smul c α.1)

theorem b3Forms_dL_dL (α : b3Forms_Ω E M k) : b3Forms_dL (b3Forms_dL α) = 0 :=
  Subtype.ext (b3Forms_d_d α.2)

/-- **The closed `k`-forms**, the kernel of `d`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 17 (de Rham cohomology). -/
def b3Forms_closed (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (k : ℕ) :
    Submodule ℝ (b3Forms_Ω E M (k + 1)) :=
  LinearMap.ker b3Forms_dL

theorem b3Forms_closed_d_eq_zero {k : ℕ} (α : b3Forms_closed E M k) : b3Forms_d α.1.1 = 0 :=
  congrArg Subtype.val (LinearMap.mem_ker.1 α.2)

/-- **The exact `k + 1`-forms**, the image of `d`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 17 (de Rham cohomology). -/
def b3Forms_exact (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (k : ℕ) :
    Submodule ℝ (b3Forms_Ω E M (k + 1)) :=
  LinearMap.range (b3Forms_dL (k := k))

theorem b3Forms_exact_le_closed (k : ℕ) : b3Forms_exact E M k ≤ b3Forms_closed E M k := by
  rintro _ ⟨α, rfl⟩
  exact b3Forms_dL_dL α

/-- **The de Rham cohomology** `Hᵏ⁺¹_dR(M)`: closed forms modulo exact forms.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 17 (de Rham cohomology). -/
abbrev b3Forms_deRham (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (k : ℕ) :
    Type _ :=
  b3Forms_closed E M k ⧸ (b3Forms_exact E M k).comap (b3Forms_closed E M k).subtype

end Forms

end HodgeLean.Foundations.Program
