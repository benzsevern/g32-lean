import HodgeLean.Foundations.Program.CurveJacobianFormsFinite

/-!
# Track B3 foundations (stage B3.4c, first steps): the Hodge star on a Riemann surface

* `b3Forms_starPt`, `b3Forms_star`: the Hodge star `(⋆α)(v) = -α(i v)` on real `1`-forms of a
  Riemann surface; it commutes with holomorphic changes of coordinates (`b3Forms_loc_star`),
  preserves smoothness and satisfies `⋆⋆ = -1`;
* `⋆ Re θ = Im θ` for holomorphic `θ`, so `Re θ` is harmonic (closed and coclosed,
  `b3Forms_isHarmonic_reForm`);
* `α ∧ ⋆β` is symmetric and `α ∧ ⋆α` has density `α(e)² + α(i e)²`, so the `L²` pairing
  `∫ α ∧ ⋆β` is positive definite on smooth `1`-forms (`b3Forms_integral_wedge_star_pos`);
* harmonic functions on a compact Riemann surface are locally constant
  (`b3Forms_d_eq_zero_of_harmonic`), by Stokes' theorem.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Linear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex structure `v ↦ i v` of `E` as a real-linear map.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (the conjugate differential and
harmonic forms); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0.6. -/
def b3Forms_J : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

theorem b3Forms_J_apply (v : E) : b3Forms_J v = Complex.I • v := rfl

/-- **The Hodge star on `1`-forms** of a complex line, `(⋆A)(v) = -A(i v)`. -/
def b3Forms_starPt (A : E [⋀^Fin 1]→L[ℝ] ℝ) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  -A.compContinuousLinearMap b3Forms_J

theorem b3Forms_starPt_apply (A : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    b3Forms_starPt A (fun _ ↦ v) = -A (fun _ ↦ Complex.I • v) := rfl

theorem b3Forms_apply_neg_const (A : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    A (fun _ ↦ -v) = -A (fun _ ↦ v) := by
  rw [show (fun _ : Fin 1 ↦ -v) = fun _ ↦ (-1 : ℝ) • v by simp, b3Forms_apply_smul_const]
  ring

theorem b3Forms_starPt_starPt (A : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_starPt (b3Forms_starPt A) = -A := by
  ext v
  have : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [this, b3Forms_starPt_apply, b3Forms_starPt_apply, smul_smul, Complex.I_mul_I,
    show ((-1 : ℂ) • v 0) = -(v 0) by simp, b3Forms_apply_neg_const]
  simp

/-- The Hodge star as a continuous linear map.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (the conjugate differential and
harmonic forms); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0.6. -/
def b3Forms_starL : (E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  -compContinuousLinearMapCLM b3Forms_J

theorem b3Forms_starL_apply (A : E [⋀^Fin 1]→L[ℝ] ℝ) : b3Forms_starL A = b3Forms_starPt A := rfl

/-- The Hodge star commutes with pullback along a complex-linear map. -/
theorem b3Forms_starPt_comp (A : E [⋀^Fin 1]→L[ℝ] ℝ) (L : E →L[ℂ] E) :
    (b3Forms_starPt A).compContinuousLinearMap (L.restrictScalars ℝ) =
      b3Forms_starPt (A.compContinuousLinearMap (L.restrictScalars ℝ)) := by
  ext v
  simp only [b3Forms_starPt, ContinuousAlternatingMap.neg_apply, compContinuousLinearMap_apply]
  simp only [ContinuousAlternatingMap.neg_apply, compContinuousLinearMap_apply,
    Function.comp_def]
  congr 2
  funext i
  simp only [b3Forms_J_apply, ContinuousLinearMap.coe_restrictScalars']
  exact (L.map_smul Complex.I (v i)).symm

/-- An alternating `2`-form on a real plane is determined by its value on a basis. -/
theorem b3Forms_alt_ext_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : Module.Basis (Fin 2) ℝ F) {w₁ w₂ : F [⋀^Fin 2]→L[ℝ] ℝ} (h : w₁ b = w₂ b) :
    w₁ = w₂ := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [w₁.toAlternatingMap.eq_smul_basis_det b, w₂.toAlternatingMap.eq_smul_basis_det b]
  exact congrArg (· • b.det) h

variable [FiniteDimensional ℂ E]

/-- **The density of `A ∧ ⋆A`** in the basis `(e, i e)` is `A(e)² + A(i e)²`. -/
theorem b3Forms_wedge_starPt_basis (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0)
    (A B : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedge A (b3Forms_starPt B) (b3Forms_cplxBasis hE he) =
      A (fun _ ↦ e) * B (fun _ ↦ e) + A (fun _ ↦ Complex.I • e) * B (fun _ ↦ Complex.I • e) := by
  rw [b3Forms_wedge_apply, b3Forms_cplxBasis_zero, b3Forms_cplxBasis_one, b3Forms_starPt_apply,
    b3Forms_starPt_apply, smul_smul, Complex.I_mul_I, show ((-1 : ℂ) • e) = -e by simp,
    b3Forms_apply_neg_const]
  ring

/-- `A ∧ ⋆B` is symmetric in `A` and `B`. -/
theorem b3Forms_wedge_starPt_comm (hE : Module.finrank ℂ E = 1) (A B : E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedge A (b3Forms_starPt B) = b3Forms_wedge B (b3Forms_starPt A) := by
  obtain ⟨e, he, -⟩ := finrank_eq_one_iff'.1 hE
  refine b3Forms_alt_ext_basis (b3Forms_cplxBasis hE he) ?_
  rw [b3Forms_wedge_starPt_basis, b3Forms_wedge_starPt_basis]
  ring

/-- A real-linear `1`-form on a complex line vanishing on `e` and `i e` is zero. -/
theorem b3Forms_eq_zero_of_basis (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0)
    {A : E [⋀^Fin 1]→L[ℝ] ℝ} (h0 : A (fun _ ↦ e) = 0) (h1 : A (fun _ ↦ Complex.I • e) = 0) :
    A = 0 := by
  have h : (b3Forms_toCLM A : E →ₗ[ℝ] ℝ) = 0 := (b3Forms_cplxBasis hE he).ext fun i ↦ by
    fin_cases i
    · simpa [b3Forms_toCLM_apply, b3Forms_cplxBasis_zero] using h0
    · simpa [b3Forms_toCLM_apply, b3Forms_cplxBasis_one] using h1
  have h' : b3Forms_toCLM A = 0 := ContinuousLinearMap.coe_injective (by simpa using h)
  have := congrArg (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)) h'
  rw [_root_.map_zero] at this
  simpa [b3Forms_toCLM] using this

end Linear

section Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

/-- **The Hodge star of a `1`-form** on a Riemann surface, pointwise `⋆`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (the conjugate differential and
harmonic forms); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0.6. -/
def b3Forms_star (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) : C → E [⋀^Fin 1]→L[ℝ] ℝ :=
  fun z ↦ b3Forms_starPt (α z)

theorem b3Forms_loc_star (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) {x : C} {u : E}
    (hu : u ∈ (chartAt E x).target) :
    b3Forms_loc (b3Forms_star α) x u = b3Forms_starPt (b3Forms_loc α x u) := by
  simp only [b3Forms_loc, b3Forms_star]
  rw [b3Forms_fderiv_tr_real (b3Forms_mem_trDom_self hu)]
  exact b3Forms_starPt_comp _ _

theorem b3Forms_IsSmooth.star {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) :
    b3Forms_IsSmooth (b3Forms_star α) := fun x ↦
  (b3Forms_starL.contDiff.comp_contDiffOn (hα x)).congr fun u hu ↦ by
    rw [b3Forms_loc_star α hu]; rfl

theorem b3Forms_star_star (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_star (b3Forms_star α) = -α := by
  funext z
  exact b3Forms_starPt_starPt _

/-- `⋆ Re θ = Im θ` for a holomorphic form `θ`. -/
theorem b3Forms_star_reForm (θ : b3_HolForm E C) :
    b3Forms_star (b3Forms_reForm θ) = b3Forms_imForm θ := by
  funext z
  ext v
  have : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [this, b3Forms_star, b3Forms_starPt_apply, b3Forms_reForm_apply, b3Forms_imForm_apply,
    ← b3Forms_holCLM_apply, ← b3Forms_holCLM_apply, map_smul, smul_eq_mul]
  simp

/-- **Harmonic `1`-forms**: smooth, closed and coclosed.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (the conjugate differential and
harmonic forms); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0.6. -/
def b3Forms_IsHarmonic (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) : Prop :=
  b3Forms_IsSmooth α ∧ b3Forms_d α = 0 ∧ b3Forms_d (b3Forms_star α) = 0

/-- **The real part of a holomorphic form is harmonic.** -/
theorem b3Forms_isHarmonic_reForm (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    b3Forms_IsHarmonic (b3Forms_reForm θ) :=
  ⟨b3Forms_isSmooth_reForm θ, b3Forms_d_reForm hE θ, by
    rw [b3Forms_star_reForm]; exact b3Forms_d_imForm hE θ⟩

/-- The local representative of a form vanishes at a point only if the form does. -/
theorem b3Forms_loc_ne_zero (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) {x z : C}
    (hz : z ∈ (chartAt E x).source) (h : α z ≠ 0) :
    b3Forms_loc α x (chartAt E x z) ≠ 0 := by
  intro h0
  apply h
  have hu := (chartAt E x).map_source hz
  have hu' : chartAt E x z ∈ b3Forms_trDom x z := by
    have := b3Forms_mem_trDom_self (E := E) hu
    rwa [(chartAt E x).left_inv hz] at this
  set L := fderiv ℂ (b3Forms_tr (E := E) x z) (chartAt E x z)
  have hdet := b3Forms_det_fderiv_tr_complex_ne_zero hu'
  have hsurj : Function.Surjective (L : E →ₗ[ℂ] E) :=
    ((Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))).2
  ext v
  obtain ⟨w, hw⟩ := hsurj (v 0)
  have hv : v = fun _ ↦ L w := funext fun i ↦ by fin_cases i; exact hw.symm
  have h1 := congrArg (fun A : E [⋀^Fin 1]→L[ℝ] ℝ ↦ A (fun _ ↦ w)) h0
  simp only [b3Forms_loc_chart α hz, compContinuousLinearMap_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at h1
  rw [b3Forms_fderiv_tr_real hu'] at h1
  rw [hv]
  exact h1

variable (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0)
include hE he

theorem b3Forms_density_wedge_star (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) {x : C} {u : E}
    (hu : u ∈ (chartAt E x).target) :
    b3Forms_loc (b3Forms_wedgeForm α (b3Forms_star α)) x u (b3Forms_cplxBasis hE he) =
      b3Forms_loc α x u (fun _ ↦ e) ^ 2 + b3Forms_loc α x u (fun _ ↦ Complex.I • e) ^ 2 := by
  rw [b3Forms_loc_wedgeForm]
  show b3Forms_wedge (b3Forms_loc α x u) (b3Forms_loc (b3Forms_star α) x u) _ = _
  rw [b3Forms_loc_star α hu, b3Forms_wedge_starPt_basis]
  ring

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

/-- **`∫ α ∧ ⋆α > 0`** for a nonzero smooth `1`-form on a compact Riemann surface: the
`L²` inner product of `1`-forms is positive definite. -/
theorem b3Forms_integral_wedge_star_pos {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    {z₀ : C} (hz₀ : α z₀ ≠ 0) :
    0 < b3Forms_integral (b3Forms_cplxBasis hE he) (b3Forms_wedgeForm α (b3Forms_star α)) := by
  refine b3Forms_integral_pos _ (hα.wedgeForm hα.star) (fun x u hu ↦ ?_) z₀ fun x hx ↦ ?_
  · rw [b3Forms_density_wedge_star hE he α hu]
    positivity
  · rw [b3Forms_density_wedge_star hE he α ((chartAt E x).map_source hx)]
    set a := b3Forms_loc α x (chartAt E x z₀) (fun _ ↦ e)
    set c := b3Forms_loc α x (chartAt E x z₀) (fun _ ↦ Complex.I • e)
    by_contra hle
    have h0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
    have h1 : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
    exact b3Forms_loc_ne_zero α hx hz₀ (b3Forms_eq_zero_of_basis hE he h0 h1)

/-- **Harmonic functions on a compact Riemann surface are locally constant**: if
`d ⋆ dg = 0` then `dg = 0`, since `∫ dg ∧ ⋆dg = ∫ d(g ⋆dg) = 0`. -/
theorem b3Forms_d_eq_zero_of_harmonic {g : C → ℝ}
    (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g))
    (hΔ : b3Forms_d (b3Forms_star (b3Forms_d (b3Forms_fun (E := E) g))) = 0) :
    b3Forms_d (b3Forms_fun (E := E) g) = 0 := by
  by_contra hne
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, b3Forms_d (b3Forms_fun (E := E) g) z₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hpos := b3Forms_integral_wedge_star_pos hE he hg.d hz₀
  have hL := b3Forms_d_smulFun hg hg.d.star
  rw [hΔ] at hL
  have h0 : b3Forms_smulFun g (0 : C → E [⋀^Fin 2]→L[ℝ] ℝ) = 0 := by
    funext z; simp [b3Forms_smulFun]
  rw [h0, add_zero] at hL
  have hS := b3Forms_integral_d_eq_zero (b3Forms_oriented_complex (C := C))
    (b3Forms_cplxBasis hE he) (b3Forms_IsSmooth.smulFun' hg hg.d.star)
  rw [hL] at hS
  exact (ne_of_gt hpos) hS

end Manifold

end HodgeLean.Foundations.Program
