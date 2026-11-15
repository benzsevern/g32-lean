import HodgeLean.Foundations.Program.CurveJacobianFormsHodgeStar
import HodgeLean.Foundations.Program.CurveJacobianFormsPairing
import HodgeLean.Foundations.Program.CurveJacobianRestLocal
import Mathlib.Analysis.InnerProductSpace.Completion

/-! # Track B3, lane Rest: the `L²` inner product on smooth `1`-forms

On a compact Riemann surface `C`, `⟨α, β⟩ = ∫_C α ∧ ⋆β` is an inner product on the smooth real
`1`-forms (`b3Rest_SF`, a type synonym for `Ω¹(C)` carrying only this structure): it is symmetric
(`α ∧ ⋆β = β ∧ ⋆α` pointwise), and positive definite since `α ∧ ⋆α` has density
`α(e)² + α(i e)²`. Its completion `b3Rest_L2` is a real Hilbert space.

The integrals use the real basis `(e, i e)` of the model line, for a fixed `e ≠ 0`
(`b3Rest_e`), and any Borel measurable structure on the model.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- A fixed nonzero vector of the model line. -/
def b3Rest_e (hE : Module.finrank ℂ E = 1) : E := (Module.finBasisOfFinrankEq ℂ E hE) 0

theorem b3Rest_e_ne_zero (hE : Module.finrank ℂ E = 1) : b3Rest_e hE ≠ 0 :=
  (Module.finBasisOfFinrankEq ℂ E hE).ne_zero 0

/-- The real basis `(e, i e)` used for integration. -/
abbrev b3Rest_b (hE : Module.finrank ℂ E = 1) : Module.Basis (Fin 2) ℝ E :=
  b3Forms_cplxBasis hE (b3Rest_e_ne_zero hE)

attribute [local instance] b3Forms_isManifold_real

variable (E C) in
/-- **The smooth real `1`-forms**, as a type carrying only the `L²` structure. -/
def b3Rest_SF : Type := ↥(b3Forms_Ω E C 1)

instance : AddCommGroup (b3Rest_SF E C) := inferInstanceAs (AddCommGroup ↥(b3Forms_Ω E C 1))

instance : Module ℝ (b3Rest_SF E C) := inferInstanceAs (Module ℝ ↥(b3Forms_Ω E C 1))

/-- The form underlying an element of `b3Rest_SF`. -/
def b3Rest_SF.form (α : b3Rest_SF E C) : C → E [⋀^Fin 1]→L[ℝ] ℝ := (α : ↥(b3Forms_Ω E C 1)).1

theorem b3Rest_SF.isSmooth (α : b3Rest_SF E C) : b3Forms_IsSmooth α.form :=
  (α : ↥(b3Forms_Ω E C 1)).2

/-- An element of `b3Rest_SF` from a smooth form. -/
def b3Rest_SF.mk (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α) : b3Rest_SF E C :=
  (⟨α, hα⟩ : ↥(b3Forms_Ω E C 1))

@[simp] theorem b3Rest_SF.form_mk (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α) :
    (b3Rest_SF.mk α hα).form = α := rfl

@[simp] theorem b3Rest_SF.form_add (α β : b3Rest_SF E C) : (α + β).form = α.form + β.form := rfl

@[simp] theorem b3Rest_SF.form_smul (c : ℝ) (α : b3Rest_SF E C) : (c • α).form = c • α.form := rfl

@[simp] theorem b3Rest_SF.form_zero : (0 : b3Rest_SF E C).form = 0 := rfl

@[simp] theorem b3Rest_SF.form_sub (α β : b3Rest_SF E C) : (α - β).form = α.form - β.form := rfl

theorem b3Rest_SF.ext {α β : b3Rest_SF E C} (h : α.form = β.form) : α = β :=
  Subtype.ext h

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

/-- **The pairing `∫ α ∧ ⋆β`** of two `1`-forms. -/
def b3Rest_inner (hE : Module.finrank ℂ E = 1) (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ) : ℝ :=
  b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α (b3Forms_star β))

theorem b3Rest_inner_comm (hE : Module.finrank ℂ E = 1) (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Rest_inner hE α β = b3Rest_inner hE β α := by
  unfold b3Rest_inner
  congr 1
  funext z
  exact b3Forms_wedge_starPt_comm hE _ _

theorem b3Rest_inner_add_left (hE : Module.finrank ℂ E = 1) {α α' β : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (hα' : b3Forms_IsSmooth α') (hβ : b3Forms_IsSmooth β) :
    b3Rest_inner hE (α + α') β = b3Rest_inner hE α β + b3Rest_inner hE α' β := by
  unfold b3Rest_inner
  have : b3Forms_wedgeForm (α + α') (b3Forms_star β) =
      b3Forms_wedgeForm α (b3Forms_star β) + b3Forms_wedgeForm α' (b3Forms_star β) := by
    funext z
    exact b3Forms_wedge_add_left _ _ _
  rw [this, b3Forms_integral_add _ (hα.wedgeForm hβ.star) (hα'.wedgeForm hβ.star)]

theorem b3Rest_inner_smul_left (hE : Module.finrank ℂ E = 1) (c : ℝ)
    (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Rest_inner hE (c • α) β = c * b3Rest_inner hE α β := by
  unfold b3Rest_inner
  have : b3Forms_wedgeForm (c • α) (b3Forms_star β) =
      c • b3Forms_wedgeForm α (b3Forms_star β) := by
    funext z
    exact b3Forms_wedge_smul_left _ _ _
  rw [this, b3Forms_integral_smul]

theorem b3Rest_inner_self_nonneg (hE : Module.finrank ℂ E = 1) (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    0 ≤ b3Rest_inner hE α α := by
  refine b3Forms_integral_nonneg _ fun x u hu ↦ ?_
  rw [b3Forms_density_wedge_star hE (b3Rest_e_ne_zero hE) α hu]
  positivity

theorem b3Rest_eq_zero_of_inner_self (hE : Module.finrank ℂ E = 1)
    {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (h : b3Rest_inner hE α α = 0) :
    α = 0 := by
  by_contra hne
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, α z₀ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hne (funext h')
  exact (ne_of_gt (b3Forms_integral_wedge_star_pos hE (b3Rest_e_ne_zero hE) hα hz₀)) h

/-! ## The completion and the exact and coexact subspaces -/

variable [hE1 : Fact (Module.finrank ℂ E = 1)]

instance : Inner ℝ (b3Rest_SF E C) := ⟨fun α β ↦ b3Rest_inner hE1.out α.form β.form⟩

theorem b3Rest_SF.inner_def (α β : b3Rest_SF E C) :
    inner ℝ α β = b3Rest_inner hE1.out α.form β.form := rfl

instance : NormedAddCommGroup (b3Rest_SF E C) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (b3Rest_SF E C) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun α β ↦ by
        simp only [starRingEnd_apply, star_trivial]
        exact b3Rest_inner_comm hE1.out _ _
      re_inner_nonneg := fun α ↦ b3Rest_inner_self_nonneg hE1.out _
      add_left := fun α α' β ↦ b3Rest_inner_add_left hE1.out α.isSmooth α'.isSmooth β.isSmooth
      smul_left := fun α β c ↦ by
        simp only [starRingEnd_apply, star_trivial]
        exact b3Rest_inner_smul_left hE1.out c _ _
      definite := fun α h ↦ b3Rest_SF.ext (by
        rw [b3Rest_SF.form_zero]
        exact b3Rest_eq_zero_of_inner_self hE1.out α.isSmooth h) }

instance : InnerProductSpace ℝ (b3Rest_SF E C) :=
  InnerProductSpace.ofCore _

variable (E C) in
/-- **The Hilbert space of `L²` real `1`-forms**, the completion of the smooth ones. -/
abbrev b3Rest_L2 : Type := UniformSpace.Completion (b3Rest_SF E C)

/-- The smooth functions. -/
def b3Rest_SmoothFun (g : C → ℝ) : Prop := b3Forms_IsSmooth (b3Forms_fun (E := E) g)

/-- The exact form `d g`. -/
def b3Rest_dSF {g : C → ℝ} (hg : b3Rest_SmoothFun (E := E) g) : b3Rest_SF E C :=
  b3Rest_SF.mk (b3Forms_d (b3Forms_fun (E := E) g)) hg.d

/-- The coexact form `⋆d g`. -/
def b3Rest_sdSF {g : C → ℝ} (hg : b3Rest_SmoothFun (E := E) g) : b3Rest_SF E C :=
  b3Rest_SF.mk (b3Forms_star (b3Forms_d (b3Forms_fun (E := E) g))) hg.d.star

variable (E C) in
/-- **The closure of the exact forms** in `L²`. -/
def b3Rest_Ex : Submodule ℝ (b3Rest_L2 E C) :=
  (Submodule.span ℝ (Set.range fun g : {g : C → ℝ // b3Rest_SmoothFun (E := E) g} ↦
    ((b3Rest_dSF g.2 : b3Rest_SF E C) : b3Rest_L2 E C))).topologicalClosure

variable (E C) in
/-- **The closure of the coexact forms** in `L²`. -/
def b3Rest_Co : Submodule ℝ (b3Rest_L2 E C) :=
  (Submodule.span ℝ (Set.range fun g : {g : C → ℝ // b3Rest_SmoothFun (E := E) g} ↦
    ((b3Rest_sdSF g.2 : b3Rest_SF E C) : b3Rest_L2 E C))).topologicalClosure

/-- `⟨α, ⋆dg⟩ = 0` for a closed form `α` (Stokes). -/
theorem b3Rest_inner_sdSF_eq_zero {α : b3Rest_SF E C} (hdα : b3Forms_d α.form = 0) {g : C → ℝ}
    (hg : b3Rest_SmoothFun (E := E) g) : inner ℝ α (b3Rest_sdSF hg) = 0 := by
  rw [b3Rest_SF.inner_def, b3Rest_inner]
  show b3Forms_integral (b3Rest_b hE1.out)
    (b3Forms_wedgeForm α.form (b3Forms_star (b3Forms_star (b3Forms_d (b3Forms_fun g))))) = 0
  rw [b3Forms_star_star]
  have h := b3Forms_integral_wedge_d_eq_zero (b3Rest_b hE1.out) (b3Forms_oriented_complex (C := C))
    hg α.isSmooth hdα
  rw [b3Forms_pairing] at h
  have : b3Forms_wedgeForm α.form (-b3Forms_d (b3Forms_fun (E := E) g)) =
      b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g)) α.form := by
    funext z
    simp only [b3Forms_wedgeForm, Pi.neg_apply]
    rw [show -b3Forms_d (b3Forms_fun (E := E) g) z = (-1 : ℝ) • b3Forms_d (b3Forms_fun g) z by
      simp, b3Forms_wedge_smul_right, b3Forms_wedge_comm, neg_one_smul, neg_neg]
  rw [this]
  exact h

/-- A vector orthogonal to a set is orthogonal to the closure of its span. -/
theorem b3Rest_inner_closure_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Set H} {y : H} (h : ∀ s ∈ S, inner ℝ s y = 0) {x : H}
    (hx : x ∈ (Submodule.span ℝ S).topologicalClosure) : inner ℝ x y = 0 := by
  have hle : (Submodule.span ℝ S).topologicalClosure ≤ (ℝ ∙ y)ᗮ :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun s hs ↦
      Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h s hs)) (Submodule.isClosed_orthogonal _)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hx)

/-- **Exact and coexact forms are orthogonal.** -/
theorem b3Rest_Ex_inner_Co {x y : b3Rest_L2 E C} (hx : x ∈ b3Rest_Ex E C) (hy : y ∈ b3Rest_Co E C) :
    inner ℝ x y = 0 := by
  rw [real_inner_comm]
  refine b3Rest_inner_closure_eq_zero ?_ hy
  rintro _ ⟨g, rfl⟩
  rw [real_inner_comm]
  refine b3Rest_inner_closure_eq_zero ?_ hx
  rintro _ ⟨f, rfl⟩
  rw [UniformSpace.Completion.inner_coe]
  exact b3Rest_inner_sdSF_eq_zero (α := b3Rest_dSF f.2) (b3Forms_d_d f.2) g.2

/-- **Closed forms are orthogonal to the coexact forms.** -/
theorem b3Rest_closed_inner_Co {α : b3Rest_SF E C} (hdα : b3Forms_d α.form = 0) {y : b3Rest_L2 E C}
    (hy : y ∈ b3Rest_Co E C) : inner ℝ (α : b3Rest_L2 E C) y = 0 := by
  rw [real_inner_comm]
  refine b3Rest_inner_closure_eq_zero ?_ hy
  rintro _ ⟨g, rfl⟩
  rw [real_inner_comm, UniformSpace.Completion.inner_coe]
  exact b3Rest_inner_sdSF_eq_zero hdα g.2

instance : (b3Rest_Ex E C).HasOrthogonalProjection := by
  have : CompleteSpace (b3Rest_Ex E C) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- **A closed form is an exact limit plus a weakly harmonic form**: `α = e + h` with
`e ∈ cl(d C^∞)` and `h ⊥ d C^∞, ⋆d C^∞`. -/
theorem b3Rest_decomp {α : b3Rest_SF E C} (hdα : b3Forms_d α.form = 0) :
    ∃ e ∈ b3Rest_Ex E C, (α : b3Rest_L2 E C) - e ∈ (b3Rest_Ex E C)ᗮ ∧
      (α : b3Rest_L2 E C) - e ∈ (b3Rest_Co E C)ᗮ := by
  set e := (b3Rest_Ex E C).starProjection (α : b3Rest_L2 E C)
  have he : e ∈ b3Rest_Ex E C := Submodule.starProjection_apply_mem _ _
  refine ⟨e, he, Submodule.sub_starProjection_mem_orthogonal _, ?_⟩
  rw [Submodule.mem_orthogonal']
  intro y hy
  rw [inner_sub_left, b3Rest_closed_inner_Co hdα hy, b3Rest_Ex_inner_Co he hy, sub_zero]

end HodgeLean.Foundations.Program
