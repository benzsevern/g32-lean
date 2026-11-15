import HodgeLean.Foundations.Program.CurveJacobianFormsRiemann
import HodgeLean.Foundations.Program.CurveJacobianFormsDeRham
import HodgeLean.Foundations.Program.CurveJacobianDefs

/-!
# Track B3 foundations (stages B3.4a, B3.6d): holomorphic forms as closed real forms

For a holomorphic `1`-form `θ ∈ Ω¹(C) = b3_HolForm E C` on a Riemann surface:
* `b3Forms_chartVec x w`, the constant vector field `w` in the chart at `x`, is holomorphic into
  the tangent bundle (`b3Forms_contMDiffOn_chartVec`), so `θ` read in a chart is holomorphic;
* `b3Forms_reForm θ`, `b3Forms_imForm θ` are smooth real `1`-forms
  (`b3Forms_isSmooth_reForm`), and closed on a complex line (`b3Forms_d_reForm`): the complex
  derivative of `θ` in a chart is a symmetric bilinear form;
* `b3Forms_cplxBasis` is the oriented real basis `(e, i e)`, in which `Re θ ∧ Im θ` has density
  `|θ(e)|²` (`b3Forms_chartDensity_reIm`);
* **Riemann positivity** (`b3Forms_integral_reIm_pos`): `∫_C Re θ ∧ Im θ > 0` for `θ ≠ 0` on a
  compact Riemann surface, i.e. `i ∫_C θ ∧ θ̄ > 0`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

section Charts

theorem b3Forms_fderiv_tr_comp_complex {x y z : C} {u : E} (hu : u ∈ b3Forms_trDom x y)
    (hz : (chartAt E x).symm u ∈ (chartAt E z).source) :
    fderiv ℂ (b3Forms_tr (E := E) x z) u =
      (fderiv ℂ (b3Forms_tr y z) (b3Forms_tr x y u)).comp (fderiv ℂ (b3Forms_tr x y) u) := by
  rw [← (b3Forms_tr_comp_eventuallyEq (z := z) hu).fderiv_eq]
  refine fderiv_comp _ (b3Forms_differentiableAt_tr_complex ?_)
    (b3Forms_differentiableAt_tr_complex hu)
  exact ⟨b3Forms_tr_mem_target hu, by rw [mem_preimage, b3Forms_symm_tr hu]; exact hz⟩

theorem b3Forms_fderiv_tr_real {x y : C} {u : E} (hu : u ∈ b3Forms_trDom x y) :
    fderiv ℝ (b3Forms_tr (E := E) x y) u =
      (fderiv ℂ (b3Forms_tr (E := E) x y) u).restrictScalars ℝ :=
  (b3Forms_differentiableAt_tr_complex hu).fderiv_restrictScalars ℝ

/-- The tangent vector at `(chartAt x).symm u` with coordinates `w` in the chart at `x`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (holomorphic 1-forms) and §19 (harmonic
forms and H¹). -/
def b3Forms_chartVec (x : C) (w : E) (u : E) : TangentBundle 𝓘(ℂ, E) C :=
  ⟨(chartAt E x).symm u, fderiv ℂ (b3Forms_tr x ((chartAt E x).symm u)) u w⟩

/-- **A constant vector field in a chart is holomorphic** as a map into the tangent bundle. -/
theorem b3Forms_contMDiffOn_chartVec (x : C) (w : E) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E).tangent ω (b3Forms_chartVec x w) (chartAt E x).target := by
  intro u₀ hu₀
  set z₀ := (chartAt E x).symm u₀
  have hO : (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' (chartAt E z₀).source ∈ 𝓝 u₀ :=
    (b3Forms_isOpen_trDom x z₀).mem_nhds (b3Forms_mem_trDom_self hu₀)
  refine (ContMDiffAt.contMDiffWithinAt ?_)
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨(contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (n := ω) (x := x)).contMDiffAt
    ((chartAt E x).open_target.mem_nhds hu₀), ?_⟩
  have hfd : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun u ↦ fderiv ℂ (b3Forms_tr (E := E) x z₀) u w)
      u₀ := by
    have h := ((b3Forms_contDiffOn_tr_complex x z₀).fderiv_of_isOpen (b3Forms_isOpen_trDom x z₀)
      (m := ω) le_rfl).contDiffAt hO
    exact (h.clm_apply contDiffAt_const).contMDiffAt
  refine hfd.congr_of_eventuallyEq ?_
  filter_upwards [hO] with u hu
  simp only [b3Forms_chartVec, TangentBundle.trivializationAt_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, fderivWithin_univ,
    Function.id_comp, Function.comp_id]
  rw [b3Forms_fderiv_tr_comp_complex (z := z₀) (b3Forms_mem_trDom_self hu.1) hu.2]
  rfl

end Charts

section OneForms

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A family of alternating `1`-forms on a finite-dimensional space is smooth when all its
evaluations are. -/
theorem b3Forms_contDiffOn_of_apply {g : G → F [⋀^Fin 1]→L[ℝ] ℝ} {s : Set G}
    (h : ∀ w : F, ContDiffOn ℝ ∞ (fun u ↦ g u (fun _ ↦ w)) s) : ContDiffOn ℝ ∞ g s := by
  set bR := Module.finBasis ℝ F
  let L : (F [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ ContinuousAlternatingMap.apply ℝ F ℝ (fun _ ↦ bR i)
  refine b3Forms_contDiffOn_of_injective L (fun A B hAB ↦ ?_) (contDiffOn_pi.2 fun i ↦ h (bR i))
  have h1 : (b3Forms_toCLM A : F →ₗ[ℝ] ℝ) = (b3Forms_toCLM B : F →ₗ[ℝ] ℝ) :=
    bR.ext fun i ↦ congrFun hAB i
  have h2 : b3Forms_toCLM A = b3Forms_toCLM B := ContinuousLinearMap.coe_injective h1
  exact (ofSubsingletonLIE (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).symm.injective h2

end OneForms

section HolForm

variable [FiniteDimensional ℂ E]

theorem b3Forms_hol_congr (θ : b3_HolForm E C) (z : C) {v w : TangentSpace 𝓘(ℂ, E) z}
    (h : v = w) : θ.1 ⟨z, v⟩ = θ.1 ⟨z, w⟩ := by rw [h]

theorem b3Forms_hol_zero (θ : b3_HolForm E C) (z : C) :
    θ.1 ⟨z, (0 : TangentSpace 𝓘(ℂ, E) z)⟩ = 0 := by
  have h := θ.2.2 z 1 0 0
  rw [b3Forms_hol_congr θ z (show (1 : ℂ) • (0 : TangentSpace 𝓘(ℂ, E) z) + 0 = 0 by simp),
    one_mul] at h
  linear_combination -h

/-- **The value of a holomorphic form at a point**, a `ℂ`-linear functional on the tangent
space.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (holomorphic 1-forms) and §19 (harmonic
forms and H¹). -/
def b3Forms_holCLM (θ : b3_HolForm E C) (z : C) : E →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ θ.1 ⟨z, v⟩
      map_add' := fun v w ↦ by
        have h := θ.2.2 z 1 v w
        rw [one_mul] at h
        erw [one_smul] at h
        exact h
      map_smul' := fun a v ↦ by
        have h := θ.2.2 z a v 0
        rw [b3Forms_hol_zero θ z, add_zero] at h
        erw [add_zero] at h
        exact h }

theorem b3Forms_holCLM_apply (θ : b3_HolForm E C) (z : C) (v : E) :
    b3Forms_holCLM θ z v = θ.1 ⟨z, v⟩ := rfl

/-- **The real part of a holomorphic form**, a real `1`-form.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (holomorphic 1-forms) and §19 (harmonic
forms and H¹). -/
def b3Forms_reForm (θ : b3_HolForm E C) : C → E [⋀^Fin 1]→L[ℝ] ℝ :=
  fun z ↦ ofSubsingleton ℝ E ℝ (0 : Fin 1)
    (Complex.reCLM.comp ((b3Forms_holCLM θ z).restrictScalars ℝ))

/-- **The imaginary part of a holomorphic form**, a real `1`-form. -/
def b3Forms_imForm (θ : b3_HolForm E C) : C → E [⋀^Fin 1]→L[ℝ] ℝ :=
  fun z ↦ ofSubsingleton ℝ E ℝ (0 : Fin 1)
    (Complex.imCLM.comp ((b3Forms_holCLM θ z).restrictScalars ℝ))

theorem b3Forms_reForm_apply (θ : b3_HolForm E C) (z : C) (v : E) :
    b3Forms_reForm θ z (fun _ ↦ v) = (θ.1 ⟨z, v⟩).re := rfl

theorem b3Forms_imForm_apply (θ : b3_HolForm E C) (z : C) (v : E) :
    b3Forms_imForm θ z (fun _ ↦ v) = (θ.1 ⟨z, v⟩).im := rfl

theorem b3Forms_imForm_eq (θ : b3_HolForm E C) :
    b3Forms_imForm θ = b3Forms_reForm ((-Complex.I) • θ) := by
  funext z
  ext v
  have : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [this, b3Forms_imForm_apply, b3Forms_reForm_apply]
  simp

/-- The local representative of the real part of a holomorphic form, on a vector. -/
theorem b3Forms_loc_reForm_apply (θ : b3_HolForm E C) {x : C} {u : E}
    (hu : u ∈ (chartAt E x).target) (w : E) :
    b3Forms_loc (b3Forms_reForm θ) x u (fun _ ↦ w) = (θ.1 (b3Forms_chartVec x w u)).re := by
  simp only [b3Forms_loc, compContinuousLinearMap_apply]
  rw [b3Forms_fderiv_tr_real (b3Forms_mem_trDom_self hu)]
  rfl

/-- **The real part of a holomorphic form is smooth.** -/
theorem b3Forms_isSmooth_reForm (θ : b3_HolForm E C) : b3Forms_IsSmooth (b3Forms_reForm θ) := by
  intro x
  refine b3Forms_contDiffOn_of_apply fun w ↦ ?_
  have h1 : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (θ.1 ∘ b3Forms_chartVec x w) (chartAt E x).target :=
    θ.2.1.comp_contMDiffOn (b3Forms_contMDiffOn_chartVec x w)
  have h2 : ContDiffOn ℝ ∞ (fun u ↦ (θ.1 (b3Forms_chartVec x w u)).re) (chartAt E x).target :=
    Complex.reCLM.contDiff.comp_contDiffOn ((h1.contDiffOn.restrict_scalars ℝ).of_le le_top)
  exact h2.congr fun u hu ↦ b3Forms_loc_reForm_apply θ hu w

theorem b3Forms_isSmooth_imForm (θ : b3_HolForm E C) : b3Forms_IsSmooth (b3Forms_imForm θ) := by
  rw [b3Forms_imForm_eq]
  exact b3Forms_isSmooth_reForm _

theorem b3Forms_chartVec_add (θ : b3_HolForm E C) (x : C) (w w' u : E) :
    θ.1 (b3Forms_chartVec x (w + w') u) =
      θ.1 (b3Forms_chartVec x w u) + θ.1 (b3Forms_chartVec x w' u) := by
  simp only [b3Forms_chartVec, ← b3Forms_holCLM_apply, map_add]

theorem b3Forms_chartVec_smul (θ : b3_HolForm E C) (x : C) (c : ℂ) (w u : E) :
    θ.1 (b3Forms_chartVec x (c • w) u) = c * θ.1 (b3Forms_chartVec x w u) := by
  simp only [b3Forms_chartVec, ← b3Forms_holCLM_apply, map_smul, smul_eq_mul]

theorem b3Forms_differentiableAt_chartVec (θ : b3_HolForm E C) {x : C} {u : E}
    (hu : u ∈ (chartAt E x).target) (w : E) :
    DifferentiableAt ℂ (fun u' ↦ θ.1 (b3Forms_chartVec x w u')) u := by
  have h1 : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (θ.1 ∘ b3Forms_chartVec x w) (chartAt E x).target :=
    θ.2.1.comp_contMDiffOn (b3Forms_contMDiffOn_chartVec x w)
  exact (h1.contDiffOn.contDiffAt ((chartAt E x).open_target.mem_nhds hu)).differentiableAt
    (by simp)

/-- **A holomorphic form is closed**: on a complex line, the complex derivative of its local
representative is a symmetric bilinear form. -/
theorem b3Forms_d_reForm (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    b3Forms_d (b3Forms_reForm θ) = 0 := by
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.1 hE
  funext z
  set x := z
  have hu := (chartAt E x).map_source (mem_chart_source E x)
  set u := chartAt E x x
  set B : E → E →L[ℂ] ℂ := fun w ↦ fderiv ℂ (fun u' ↦ θ.1 (b3Forms_chartVec x w u')) u
  have hBs : ∀ (c : ℂ) (w : E), B (c • w) = c • B w := fun c w ↦ by
    simp only [B, b3Forms_chartVec_smul]
    exact fderiv_const_mul (b3Forms_differentiableAt_chartVec θ hu w) c
  have hsym : ∀ v₀ v₁ : E, B v₁ v₀ = B v₀ v₁ := fun v₀ v₁ ↦ by
    obtain ⟨a, rfl⟩ := he v₀
    obtain ⟨b, rfl⟩ := he v₁
    simp only [hBs, _root_.smul_apply, map_smul, smul_eq_mul]
    ring
  have hloc : ∀ w : E, (fun u' ↦ b3Forms_loc (b3Forms_reForm θ) x u' (fun _ ↦ w)) =ᶠ[𝓝 u]
      fun u' ↦ (θ.1 (b3Forms_chartVec x w u')).re := fun w ↦ by
    filter_upwards [(chartAt E x).open_target.mem_nhds hu] with u' hu'
    exact b3Forms_loc_reForm_apply θ hu' w
  have hd : ∀ w v : E, fderiv ℝ (fun u' ↦ b3Forms_loc (b3Forms_reForm θ) x u' (fun _ ↦ w)) u v =
      (B w v).re := fun w v ↦ by
    rw [(hloc w).fderiv_eq]
    have h := ((b3Forms_differentiableAt_chartVec θ hu w).restrictScalars ℝ).hasFDerivAt
    have h2 := Complex.reCLM.hasFDerivAt.comp u h
    rw [show (fun u' ↦ (θ.1 (b3Forms_chartVec x w u')).re) =
      ⇑Complex.reCLM ∘ fun u' ↦ θ.1 (b3Forms_chartVec x w u') from rfl, h2.fderiv]
    simp [B, (b3Forms_differentiableAt_chartVec θ hu w).fderiv_restrictScalars ℝ]
  show extDeriv _ _ = 0
  ext v
  rw [extDeriv_apply ((b3Forms_isSmooth_reForm θ).contDiffAt hu |>.differentiableAt (by simp)),
    Fin.sum_univ_two]
  have e0 : Fin.removeNth 0 v = fun _ ↦ v 1 := by funext i; fin_cases i; rfl
  have e1 : Fin.removeNth 1 v = fun _ ↦ v 0 := by funext i; fin_cases i; rfl
  rw [e0, e1, hd, hd, hsym (v 0) (v 1)]
  simp

theorem b3Forms_d_imForm (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    b3Forms_d (b3Forms_imForm θ) = 0 := by
  rw [b3Forms_imForm_eq]
  exact b3Forms_d_reForm hE _

theorem b3Forms_loc_imForm_apply (θ : b3_HolForm E C) {x : C} {u : E}
    (hu : u ∈ (chartAt E x).target) (w : E) :
    b3Forms_loc (b3Forms_imForm θ) x u (fun _ ↦ w) = (θ.1 (b3Forms_chartVec x w u)).im := by
  simp only [b3Forms_loc, compContinuousLinearMap_apply]
  rw [b3Forms_fderiv_tr_real (b3Forms_mem_trDom_self hu)]
  rfl

end HolForm

section Positivity

variable [FiniteDimensional ℂ E]

/-- **The oriented real basis `(e, i e)`** of a complex line.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (holomorphic 1-forms) and §19 (harmonic
forms and H¹). -/
def b3Forms_cplxBasis (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0) :
    Module.Basis (Fin 2) ℝ E :=
  basisOfLinearIndependentOfCardEqFinrank (b := ![e, Complex.I • e])
    (LinearIndependent.pair_iff.2 fun s t hst ↦ by
      have h : ((s : ℂ) + t * Complex.I) • e = 0 := by
        rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
        simpa [smul_smul] using hst
      have h' := (smul_eq_zero.1 h).resolve_right he
      have hre := congrArg Complex.re h'
      have him := congrArg Complex.im h'
      simp at hre him
      exact ⟨hre, him⟩)
    (by rw [finrank_real_of_complex, hE]; rfl)

theorem b3Forms_cplxBasis_zero (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0) :
    b3Forms_cplxBasis hE he 0 = e := by
  simp [b3Forms_cplxBasis]

theorem b3Forms_cplxBasis_one (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0) :
    b3Forms_cplxBasis hE he 1 = Complex.I • e := by
  simp [b3Forms_cplxBasis]

/-- **The density of `Re θ ∧ Im θ` in a chart** is `|θ(e)|²`. -/
theorem b3Forms_chartDensity_reIm (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0)
    (θ : b3_HolForm E C) {x : C} {u : E} (hu : u ∈ (chartAt E x).target) :
    b3Forms_loc (b3Forms_wedgeForm (b3Forms_reForm θ) (b3Forms_imForm θ)) x u
        (b3Forms_cplxBasis hE he) =
      Complex.normSq (θ.1 (b3Forms_chartVec x e u)) := by
  rw [b3Forms_loc_wedgeForm, b3Forms_wedge_apply, b3Forms_cplxBasis_zero,
    b3Forms_cplxBasis_one, b3Forms_loc_reForm_apply θ hu, b3Forms_loc_reForm_apply θ hu,
    b3Forms_loc_imForm_apply θ hu, b3Forms_loc_imForm_apply θ hu, b3Forms_chartVec_smul]
  simp [Complex.normSq_apply]

/-- A holomorphic form that is nonzero at a point is nonzero on every chart vector there. -/
theorem b3Forms_chartVec_ne_zero (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0)
    (θ : b3_HolForm E C) {x : C} {u : E} (hu : u ∈ (chartAt E x).target) {v₀ : E}
    (hv₀ : θ.1 ⟨(chartAt E x).symm u, v₀⟩ ≠ 0) :
    θ.1 (b3Forms_chartVec x e u) ≠ 0 := by
  set z := (chartAt E x).symm u
  set w := fderiv ℂ (b3Forms_tr (E := E) x z) u e
  have hdet := b3Forms_det_fderiv_tr_complex_ne_zero (b3Forms_mem_trDom_self (E := E) hu)
  have hw : w ≠ 0 := by
    intro h0
    have hinj : Function.Injective (fderiv ℂ (b3Forms_tr (E := E) x z) u : E →ₗ[ℂ] E) :=
      ((Module.End.isUnit_iff _).1
        ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))).1
    exact he (hinj (by simpa using h0))
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hw).1 hE v₀
  intro h0
  apply hv₀
  have : θ.1 ⟨z, v₀⟩ = c * θ.1 ⟨z, w⟩ := by
    rw [← b3Forms_holCLM_apply, ← b3Forms_holCLM_apply, ← hc, map_smul, smul_eq_mul]
  rw [this]
  simp only [b3Forms_chartVec] at h0
  rw [h0, mul_zero]

/-- **Two holomorphic forms wedge to zero** on a complex line, in real terms:
`θ ∧ θ' = 0` means `Re θ ∧ Re θ' = Im θ ∧ Im θ'` and `Re θ ∧ Im θ' = - Im θ ∧ Re θ'`. -/
theorem b3Forms_wedge_hol_eq (hE : Module.finrank ℂ E = 1) (θ θ' : b3_HolForm E C) :
    b3Forms_wedgeForm (b3Forms_reForm θ) (b3Forms_reForm θ') =
        b3Forms_wedgeForm (b3Forms_imForm θ) (b3Forms_imForm θ') ∧
      b3Forms_wedgeForm (b3Forms_reForm θ) (b3Forms_imForm θ') =
        -b3Forms_wedgeForm (b3Forms_imForm θ) (b3Forms_reForm θ') := by
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.1 hE
  have key : ∀ (z : C) (v : Fin 2 → E),
      θ.1 ⟨z, v 0⟩ * θ'.1 ⟨z, v 1⟩ = θ.1 ⟨z, v 1⟩ * θ'.1 ⟨z, v 0⟩ := fun z v ↦ by
    obtain ⟨a, ha⟩ := he (v 0)
    obtain ⟨c, hc⟩ := he (v 1)
    simp only [← b3Forms_holCLM_apply, ← ha, ← hc, map_smul, smul_eq_mul]
    ring
  constructor <;> funext z <;> ext v <;>
  · have hk := key z v
    have hre := congrArg Complex.re hk
    have him := congrArg Complex.im hk
    simp only [Complex.mul_re, Complex.mul_im] at hre him
    simp only [b3Forms_wedgeForm, b3Forms_wedge_apply, b3Forms_reForm_apply,
      b3Forms_imForm_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
    linarith

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

/-- **The Riemann positivity `i ∫ θ ∧ θ̄ > 0`**: for a nonzero holomorphic form `θ` on a compact
Riemann surface, `∫_C Re θ ∧ Im θ > 0` for the orientation `(e, i e)` (`i θ ∧ θ̄ = 2 Re θ ∧ Im θ`).
-/
theorem b3Forms_integral_reIm_pos (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0)
    (θ : b3_HolForm E C) (hθ : θ ≠ 0) :
    0 < b3Forms_integral (b3Forms_cplxBasis hE he)
      (b3Forms_wedgeForm (b3Forms_reForm θ) (b3Forms_imForm θ)) := by
  set b := b3Forms_cplxBasis hE he
  set η := b3Forms_wedgeForm (b3Forms_reForm θ) (b3Forms_imForm θ)
  have hη : b3Forms_IsSmooth η := (b3Forms_isSmooth_reForm θ).wedgeForm (b3Forms_isSmooth_imForm θ)
  have hval : ∀ (i : C) (u : E), u ∈ (chartAt E i).target →
      b3Forms_chartFun b i (b3Forms_smulFun (b3Forms_pou E C i) η) u =
        b3Forms_pou E C i ((chartAt E i).symm u) *
          Complex.normSq (θ.1 (b3Forms_chartVec i e u)) := fun i u hu ↦ by
    simp only [b3Forms_chartFun, indicator_of_mem hu, b3Forms_loc_smulFun,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [b3Forms_chartDensity_reIm hE he θ hu]
  have hnn : ∀ i : C, 0 ≤ b3Forms_chartFun b i (b3Forms_smulFun (b3Forms_pou E C i) η) :=
    fun i u ↦ by
      by_cases hu : u ∈ (chartAt E i).target
      · rw [hval i u hu]
        exact mul_nonneg ((b3Forms_pou E C).nonneg i _) (Complex.normSq_nonneg _)
      · simp [b3Forms_chartFun, hu]
  rw [b3Forms_integral_eq_sum]
  obtain ⟨p, hp⟩ : ∃ p : TangentBundle 𝓘(ℂ, E) C, θ.1 p ≠ 0 := by
    by_contra h
    push Not at h
    exact hθ (Subtype.ext (funext h))
  obtain ⟨i, hi⟩ := (b3Forms_pou E C).exists_pos_of_mem (mem_univ p.1)
  have hiS : i ∈ b3Forms_pouSupp E C := (Set.Finite.mem_toFinset _).2 ⟨p.1, hi.ne'⟩
  refine Finset.sum_pos' (fun j _ ↦ MeasureTheory.integral_nonneg (hnn j)) ⟨i, hiS, ?_⟩
  have hsrc : p.1 ∈ (chartAt E i).source :=
    b3Forms_pou_isSubordinate i (subset_tsupport _ hi.ne')
  set u₀ := chartAt E i p.1
  have hu₀ : u₀ ∈ (chartAt E i).target := (chartAt E i).map_source hsrc
  have hsym : (chartAt E i).symm u₀ = p.1 := (chartAt E i).left_inv hsrc
  have hsm := hη.smulFun_pou i
  have hsub : tsupport (b3Forms_smulFun (b3Forms_pou E C i) η) ⊆ (chartAt E i).source :=
    (b3Forms_tsupport_smulFun_subset_left _ _).trans (b3Forms_pou_isSubordinate i)
  have hcont := b3Forms_continuous_chartFun b (hsm i).continuousOn
    (b3Forms_isCompact_tsupport _) hsub
  have hint := b3Forms_integrable_chartFun b hsm (b3Forms_isCompact_tsupport _) hsub
  have hpos : 0 < b3Forms_chartFun b i (b3Forms_smulFun (b3Forms_pou E C i) η) u₀ := by
    rw [hval i u₀ hu₀, hsym]
    refine mul_pos hi (Complex.normSq_pos.2 (b3Forms_chartVec_ne_zero hE he θ hu₀ (v₀ := p.2) ?_))
    rw [hsym]
    exact hp
  rw [b3Forms_chartIntegral, MeasureTheory.integral_pos_iff_support_of_nonneg (hnn i) hint]
  refine lt_of_lt_of_le ((isOpen_lt continuous_const hcont).measure_pos b.addHaar ⟨u₀, hpos⟩)
    (MeasureTheory.measure_mono fun u hu ↦ ne_of_gt hu)

end Positivity

end HodgeLean.Foundations.Program
