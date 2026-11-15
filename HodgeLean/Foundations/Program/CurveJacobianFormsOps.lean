import HodgeLean.Foundations.Program.CurveJacobianFormsBasic

/-!
# Track B3 foundations (stage B3.4a): functions, wedge products and pullbacks of forms

On top of `CurveJacobianFormsBasic.lean`:
* functions as `0`-forms (`b3Forms_fun`) and their differentials;
* the wedge product of two `1`-forms (`b3Forms_wedge`), a `2`-form;
* the pullback `b3Forms_pullback f α` of forms along a smooth map `f : M → N` and its
  commutation with the exterior derivative (`b3Forms_d_pullback`). -/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The wedge product of two alternating `1`-forms**, `(a ∧ b)(v₀, v₁) = a v₀ b v₁ - a v₁ b v₀`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_wedge (a b : E [⋀^Fin 1]→L[ℝ] ℝ) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  alternatizeUncurryFin (((ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm a).smulRight b)

theorem b3Forms_wedge_apply (a b : E [⋀^Fin 1]→L[ℝ] ℝ) (v : Fin 2 → E) :
    b3Forms_wedge a b v =
      a (fun _ ↦ v 0) * b (fun _ ↦ v 1) - a (fun _ ↦ v 1) * b (fun _ ↦ v 0) := by
  simp only [b3Forms_wedge, alternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.smulRight_apply, ofSubsingleton_symm_apply_apply]
  have h0 : Fin.removeNth 0 v = fun _ ↦ v 1 := by
    funext i; fin_cases i; rfl
  have h1 : Fin.removeNth 1 v = fun _ ↦ v 0 := by
    funext i; fin_cases i; rfl
  rw [Fin.sum_univ_two, h0, h1]
  simp [sub_eq_add_neg]

theorem b3Forms_wedge_add_left (a a' b : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedge (a + a') b = b3Forms_wedge a b + b3Forms_wedge a' b := by
  ext v; simp only [b3Forms_wedge_apply, ContinuousAlternatingMap.add_apply]; ring

theorem b3Forms_wedge_add_right (a b b' : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedge a (b + b') = b3Forms_wedge a b + b3Forms_wedge a b' := by
  ext v; simp only [b3Forms_wedge_apply, ContinuousAlternatingMap.add_apply]; ring

theorem b3Forms_wedge_smul_left (c : ℝ) (a b : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedge (c • a) b = c • b3Forms_wedge a b := by
  ext v; simp only [b3Forms_wedge_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]; ring

theorem b3Forms_wedge_smul_right (c : ℝ) (a b : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedge a (c • b) = c • b3Forms_wedge a b := by
  ext v; simp only [b3Forms_wedge_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]; ring

theorem b3Forms_wedge_comm (a b : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedge b a = -b3Forms_wedge a b := by
  ext v; simp only [b3Forms_wedge_apply, ContinuousAlternatingMap.neg_apply]; ring

theorem b3Forms_wedge_self (a : E [⋀^Fin 1]→L[ℝ] ℝ) : b3Forms_wedge a a = 0 := by
  ext v; simp only [b3Forms_wedge_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]; ring

theorem b3Forms_wedge_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : E [⋀^Fin 1]→L[ℝ] ℝ) (L : F →L[ℝ] E) :
    (b3Forms_wedge a b).compContinuousLinearMap L =
      b3Forms_wedge (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [compContinuousLinearMap_apply, b3Forms_wedge_apply]
  rfl

variable [FiniteDimensional ℝ E]

/-- Continuous alternating forms on a finite-dimensional space form a finite-dimensional
space. -/
instance b3Forms_finiteDimensional_alternating {ι : Type*} [Fintype ι] :
    FiniteDimensional ℝ (E [⋀^ι]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (toContinuousMultilinearMapCLM ℝ : _ →L[ℝ] _).toLinearMap
    toContinuousMultilinearMap_injective

/-- The wedge product as a continuous bilinear map.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_wedgeL :
    (E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((E [⋀^Fin 1]→L[ℝ] ℝ) →ₗ[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) ≃ₗ[ℝ] _)
      ∘ₗ LinearMap.mk₂ ℝ b3Forms_wedge b3Forms_wedge_add_left b3Forms_wedge_smul_left
        b3Forms_wedge_add_right b3Forms_wedge_smul_right)

theorem b3Forms_wedgeL_apply (a b : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedgeL a b = b3Forms_wedge a b := rfl

theorem b3Forms_contDiffOn_wedge {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} {a b : G → E [⋀^Fin 1]→L[ℝ] ℝ} {s : Set G}
    (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s) :
    ContDiffOn ℝ n (fun u ↦ b3Forms_wedge (a u) (b u)) s :=
  (b3Forms_wedgeL.contDiff.comp_contDiffOn ha).clm_apply hb (f := fun u ↦ b3Forms_wedgeL (a u))

end Linear

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-! ### Functions as `0`-forms -/

/-- **A function as a `0`-form.**
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_fun (g : M → ℝ) : M → E [⋀^Fin 0]→L[ℝ] ℝ :=
  fun z ↦ constOfIsEmpty ℝ E (Fin 0) (g z)

theorem b3Forms_loc_fun (g : M → ℝ) (x : M) :
    b3Forms_loc (b3Forms_fun g) x =
      fun u ↦ constOfIsEmpty ℝ E (Fin 0) (g ((chartAt E x).symm u)) := by
  funext u
  ext v
  simp [b3Forms_loc, b3Forms_fun]

theorem b3Forms_isSmooth_fun_iff (g : M → ℝ) :
    b3Forms_IsSmooth (b3Forms_fun (E := E) g) ↔
      ∀ x : M, ContDiffOn ℝ ∞ (g ∘ (chartAt E x).symm) (chartAt E x).target := by
  simp only [b3Forms_IsSmooth, b3Forms_loc_fun]
  refine forall_congr' fun x ↦ ?_
  have := (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).toContinuousLinearEquiv.comp_contDiffOn_iff
    (f := g ∘ (chartAt E x).symm) (s := (chartAt E x).target) (n := ∞)
  exact this

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem b3Forms_isSmooth_fun {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) :
    b3Forms_IsSmooth (b3Forms_fun (E := E) g) := by
  rw [b3Forms_isSmooth_fun_iff]
  intro x
  exact (hg.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x))).contDiffOn

/-- **The differential of a function** in the chart at `z`. -/
theorem b3Forms_d_fun (g : M → ℝ) (z : M) :
    b3Forms_d (b3Forms_fun (E := E) g) z =
      ofSubsingleton ℝ E ℝ (0 : Fin 1)
        (fderiv ℝ (g ∘ (chartAt E z).symm) (chartAt E z z)) := by
  simp only [b3Forms_d, b3Forms_loc_fun]
  exact extDeriv_constOfIsEmpty (g ∘ (chartAt E z).symm) _

/-! ### The wedge product of `1`-forms -/

/-- **The wedge product of two families of `1`-forms.**
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_wedgeForm (α β : M → E [⋀^Fin 1]→L[ℝ] ℝ) : M → E [⋀^Fin 2]→L[ℝ] ℝ :=
  fun z ↦ b3Forms_wedge (α z) (β z)

theorem b3Forms_loc_wedgeForm (α β : M → E [⋀^Fin 1]→L[ℝ] ℝ) (x : M) :
    b3Forms_loc (b3Forms_wedgeForm α β) x =
      fun u ↦ b3Forms_wedge (b3Forms_loc α x u) (b3Forms_loc β x u) := by
  funext u
  exact b3Forms_wedge_comp _ _ _

theorem b3Forms_IsSmooth.wedgeForm [FiniteDimensional ℝ E] {α β : M → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (hβ : b3Forms_IsSmooth β) :
    b3Forms_IsSmooth (b3Forms_wedgeForm α β) := fun x ↦ by
  rw [b3Forms_loc_wedgeForm]
  exact b3Forms_contDiffOn_wedge (hα x) (hβ x)

/-- **Multiplication of a form by a function.**
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_smulFun {k : ℕ} (g : M → ℝ) (α : M → E [⋀^Fin k]→L[ℝ] ℝ) :
    M → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun z ↦ g z • α z

theorem b3Forms_loc_smulFun {k : ℕ} (g : M → ℝ) (α : M → E [⋀^Fin k]→L[ℝ] ℝ) (x : M) :
    b3Forms_loc (b3Forms_smulFun g α) x =
      fun u ↦ g ((chartAt E x).symm u) • b3Forms_loc α x u := by
  funext u
  ext v
  simp [b3Forms_loc, b3Forms_smulFun]

theorem b3Forms_IsSmooth.smulFun {k : ℕ} {g : M → ℝ} {α : M → E [⋀^Fin k]→L[ℝ] ℝ}
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hα : b3Forms_IsSmooth α) :
    b3Forms_IsSmooth (b3Forms_smulFun g α) := fun x ↦ by
  rw [b3Forms_loc_smulFun]
  exact ((hg.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x))).contDiffOn).smul
    (hα x)

theorem b3Forms_IsSmooth.smulFun' {k : ℕ} {g : M → ℝ} {α : M → E [⋀^Fin k]→L[ℝ] ℝ}
    (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g)) (hα : b3Forms_IsSmooth α) :
    b3Forms_IsSmooth (b3Forms_smulFun g α) := fun x ↦ by
  rw [b3Forms_loc_smulFun]
  exact ((b3Forms_isSmooth_fun_iff g).1 hg x).smul (hα x)

/-- The function underlying a `0`-form.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_toFun (γ : M → E [⋀^Fin 0]→L[ℝ] ℝ) : M → ℝ := fun z ↦ γ z 0

theorem b3Forms_fun_toFun (γ : M → E [⋀^Fin 0]→L[ℝ] ℝ) : b3Forms_fun (b3Forms_toFun γ) = γ := by
  funext z
  ext v
  simp only [b3Forms_fun, b3Forms_toFun, constOfIsEmpty_apply]
  congr 1
  exact Subsingleton.elim _ _

end Manifold

/-! ### Pullback along a smooth map -/

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- A map `f : M → N` written in the charts at `x` and `y`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_wr (f : M → N) (x : M) (y : N) : E → F :=
  chartAt F y ∘ f ∘ (chartAt E x).symm

/-- The domain of `b3Forms_wr f x y`. -/
def b3Forms_wrDom (f : M → N) (x : M) (y : N) : Set E :=
  (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' (f ⁻¹' (chartAt F y).source)

theorem b3Forms_isOpen_wrDom {f : M → N} (hf : Continuous f) (x : M) (y : N) :
    IsOpen (b3Forms_wrDom (E := E) (F := F) f x y) :=
  (chartAt E x).isOpen_inter_preimage_symm (hf.isOpen_preimage _ (chartAt F y).open_source)

theorem b3Forms_mem_wrDom_self (f : M → N) {x : M} {u : E} (hu : u ∈ (chartAt E x).target) :
    u ∈ b3Forms_wrDom (F := F) f x (f ((chartAt E x).symm u)) := ⟨hu, mem_chart_source F _⟩

/-- **The pullback of a family of forms** along `f : M → N`: at `z`, the value `α (f z)` composed
with the derivative of `f` in the charts at `z` and `f z`.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 14 (differential forms, the
exterior derivative, pullback); Mathlib `extDeriv`. -/
def b3Forms_pullback {k : ℕ} (f : M → N) (α : N → F [⋀^Fin k]→L[ℝ] ℝ) :
    M → E [⋀^Fin k]→L[ℝ] ℝ :=
  fun z ↦ (α (f z)).compContinuousLinearMap (fderiv ℝ (b3Forms_wr f z (f z)) (chartAt E z z))

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

local notation "𝔴" => b3Forms_wr (E := E) (F := F)
local notation "𝔇" => b3Forms_wrDom (E := E) (F := F)

theorem b3Forms_contDiffOn_wr {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (x : M) (y : N) :
    ContDiffOn ℝ ∞ (𝔴 f x y) (𝔇 f x y) := by
  have := (contMDiff_iff.1 hf).2 x y
  simpa [b3Forms_wr, b3Forms_wrDom, extChartAt, Function.comp_def] using this

theorem b3Forms_contDiffAt_wr {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) {x : M} {y : N}
    {u : E} (hu : u ∈ 𝔇 f x y) : ContDiffAt ℝ ∞ (𝔴 f x y) u :=
  (b3Forms_contDiffOn_wr hf x y).contDiffAt ((b3Forms_isOpen_wrDom hf.continuous x y).mem_nhds hu)

theorem b3Forms_wr_mem_target {f : M → N} {x : M} {y : N} {u : E}
    (hu : u ∈ 𝔇 f x y) : 𝔴 f x y u ∈ (chartAt F y).target :=
  (chartAt F y).map_source hu.2

theorem b3Forms_symm_wr {f : M → N} {x : M} {y : N} {u : E}
    (hu : u ∈ 𝔇 f x y) :
    (chartAt F y).symm (𝔴 f x y u) = f ((chartAt E x).symm u) :=
  (chartAt F y).left_inv hu.2

/-- **The chain rule for a map written in two pairs of charts.** -/
theorem b3Forms_fderiv_wr_comp {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) {x : M}
    {y : N} {u : E} (hu : u ∈ 𝔇 f x y) :
    (fderiv ℝ (𝔴 f ((chartAt E x).symm u) (f ((chartAt E x).symm u)))
        (chartAt E ((chartAt E x).symm u) ((chartAt E x).symm u))).comp
      (fderiv ℝ (b3Forms_tr x ((chartAt E x).symm u)) u) =
    (fderiv ℝ (b3Forms_tr y (f ((chartAt E x).symm u))) (𝔴 f x y u)).comp
      (fderiv ℝ (𝔴 f x y) u) := by
  set z := (chartAt E x).symm u
  have hu' : u ∈ b3Forms_trDom x z := b3Forms_mem_trDom_self hu.1
  have h1 : 𝔴 f z (f z) ∘ b3Forms_tr x z =ᶠ[𝓝 u] 𝔴 f x (f z) := by
    filter_upwards [(b3Forms_isOpen_trDom x z).mem_nhds hu'] with v hv
    simp only [Function.comp_apply, b3Forms_wr, b3Forms_tr]
    rw [(chartAt E z).left_inv hv.2]
  have h2 : b3Forms_tr y (f z) ∘ 𝔴 f x y =ᶠ[𝓝 u] 𝔴 f x (f z) := by
    filter_upwards [(b3Forms_isOpen_wrDom hf.continuous x y).mem_nhds hu] with v hv
    simp only [Function.comp_apply, b3Forms_wr, b3Forms_tr]
    rw [(chartAt F y).left_inv hv.2]
  have hz : chartAt E z z ∈ 𝔇 f z (f z) :=
    ⟨(chartAt E z).map_source (mem_chart_source E z), by
      simp [(chartAt E z).left_inv (mem_chart_source E z), mem_chart_source]⟩
  have hw : 𝔴 f x y u ∈ b3Forms_trDom (E := F) y (f z) :=
    ⟨b3Forms_wr_mem_target hu, by simp [b3Forms_symm_wr hu, z, mem_chart_source]⟩
  have e1 := fderiv_comp u ((b3Forms_contDiffAt_wr hf hz).differentiableAt (by simp))
    (b3Forms_differentiableAt_tr hu')
  rw [h1.fderiv_eq] at e1
  have e2 := fderiv_comp u (b3Forms_differentiableAt_tr hw)
    ((b3Forms_contDiffAt_wr hf hu).differentiableAt (by simp))
  rw [h2.fderiv_eq] at e2
  exact e1.symm.trans e2

/-- **The pullback in charts**: on the domain of `f` written in the charts at `x` and `y`, the
local representative of `f^* α` is the pullback of the local representative of `α`. -/
theorem b3Forms_loc_pullback {k : ℕ} {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (α : N → F [⋀^Fin k]→L[ℝ] ℝ) {x : M} {y : N} {u : E} (hu : u ∈ 𝔇 f x y) :
    b3Forms_loc (b3Forms_pullback f α) x u =
      (b3Forms_loc α y (𝔴 f x y u)).compContinuousLinearMap
        (fderiv ℝ (𝔴 f x y) u) := by
  have key := b3Forms_fderiv_wr_comp hf hu
  simp only [b3Forms_loc, b3Forms_pullback, b3Forms_symm_wr hu]
  ext v
  simp only [compContinuousLinearMap_apply]
  have := congrArg (fun L : E →L[ℝ] F ↦ ⇑L ∘ v) key
  simp only [ContinuousLinearMap.coe_comp] at this
  simp only [Function.comp_assoc] at this ⊢
  rw [this]

theorem b3Forms_IsSmooth.pullback [FiniteDimensional ℝ E] {k : ℕ} {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) {α : N → F [⋀^Fin k]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) : b3Forms_IsSmooth (b3Forms_pullback (E := E) f α) := by
  intro x u hu
  set y := f ((chartAt E x).symm u)
  have hu' : u ∈ 𝔇 f x y := b3Forms_mem_wrDom_self (E := E) (F := F) f hu
  have hO := b3Forms_isOpen_wrDom (E := E) (F := F) hf.continuous x y
  have hsm : ContDiffOn ℝ ∞ (fun u' ↦ (b3Forms_loc α y (𝔴 f x y u')).compContinuousLinearMap
      (fderiv ℝ (𝔴 f x y) u')) (𝔇 f x y) := by
    refine b3Forms_contDiffOn_comp ?_ ((b3Forms_contDiffOn_wr hf x y).fderiv_of_isOpen hO
      (by simp))
    exact (hα y).comp (b3Forms_contDiffOn_wr hf x y) fun _ h ↦ b3Forms_wr_mem_target h
  refine ((hsm.contDiffAt (hO.mem_nhds hu')).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hO.mem_nhds hu'] with v hv
  exact b3Forms_loc_pullback hf α hv

/-- **The exterior derivative commutes with pullback.** -/
theorem b3Forms_d_pullback {k : ℕ} {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    {α : N → F [⋀^Fin k]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) :
    b3Forms_d (b3Forms_pullback (E := E) f α) = b3Forms_pullback f (b3Forms_d α) := by
  funext z
  have hz := (chartAt E z).map_source (mem_chart_source E z)
  have hz' : chartAt E z z ∈ 𝔇 f z (f z) := by
    have := b3Forms_mem_wrDom_self (E := E) (F := F) f hz
    rwa [(chartAt E z).left_inv (mem_chart_source E z)] at this
  have hO := b3Forms_isOpen_wrDom (E := E) (F := F) hf.continuous z (f z)
  have h : b3Forms_loc (b3Forms_pullback f α) z =ᶠ[𝓝 (chartAt E z z)] fun u' ↦
      (b3Forms_loc α (f z) (𝔴 f z (f z) u')).compContinuousLinearMap
        (fderiv ℝ (𝔴 f z (f z)) u') := by
    filter_upwards [hO.mem_nhds hz'] with v hv
    exact b3Forms_loc_pullback hf α hv
  have hwz : 𝔴 f z (f z) (chartAt E z z) = chartAt F (f z) (f z) := by
    simp [b3Forms_wr, (chartAt E z).left_inv (mem_chart_source E z)]
  show extDeriv _ _ = _
  rw [h.extDeriv_eq, extDeriv_pullback (r := ∞) _ (b3Forms_contDiffAt_wr hf hz')
    b3Forms_minSmoothness_le, hwz]
  · rfl
  · rw [hwz]
    exact (hα.contDiffAt ((chartAt F (f z)).map_source (mem_chart_source F _))).differentiableAt
      (by simp)

end Pullback

end HodgeLean.Foundations.Program
