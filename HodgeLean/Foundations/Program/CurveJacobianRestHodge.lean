import HodgeLean.Foundations.Program.CurveJacobianRestPD

/-! # Track B3, lane Rest: the Hodge decomposition of closed `1`-forms

* Every `C¹` loop `γ` has a smooth dual form `η_γ` with `∫ ω ∧ η_γ = ∫_γ ω` for closed `ω`
  (`b3Rest_exists_dual`): the dual form of a chart polygon following `γ`.
* `⋆η_γ` is orthogonal to the `L²` closure of the exact forms, since `⟨dg, ⋆η_γ⟩ = -∫_γ dg = 0`;
  so a smooth closed form in that closure has vanishing periods and is exact
  (`b3Rest_periodsVanish_of_mem_Ex`).
* **Hodge decomposition** (`b3Rest_hodge`): a smooth closed real `1`-form is `Re θ + dg` with `θ`
  holomorphic. Split `α = e + h` with `e` in the closure of the exact forms and `h` weakly harmonic;
  by Weyl's lemma `h` is a smooth harmonic form, the real part of a holomorphic form, and
  `e = α - h` is smooth, closed, and hence exact.
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

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]

/-- **The dual form of a loop**: for a `C¹` loop `P` there is a smooth `1`-form `η` with
`∫ ω ∧ η = ∫_P ω` for every smooth closed `1`-form `ω`. -/
theorem b3Rest_exists_dual (hE : Module.finrank ℂ E = 1) {P : ℝ → C}
    (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P) (hper : Function.Periodic P 1) :
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧
      ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) = b3Forms_lineIntegral α P 0 1 := by
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ := b3Rest_exists_chartCover (E := E) P hP.continuous hper
  let K : b3Rest_Cover E P := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  obtain ⟨ch⟩ := b3Rest_exists_choice hE hper K hP
  obtain ⟨η, hη, hη'⟩ := ch.poly.exists_dual hE
  exact ⟨η, hη, fun α hα hdα ↦
    (hη' α hα hdα).trans (b3Rest_Poly.lineIntegral_loop ch.follows hP hper hα hdα)⟩

variable [hE1 : Fact (Module.finrank ℂ E = 1)]

/-- `∫ α ∧ ⋆⋆η = -∫ α ∧ η`. -/
theorem b3Rest_inner_star_eq (α : b3Rest_SF E C) {η : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hη : b3Forms_IsSmooth η) :
    inner ℝ α (b3Rest_SF.mk (b3Forms_star η) hη.star) =
      -b3Forms_integral (b3Rest_b hE1.out) (b3Forms_wedgeForm α.form η) := by
  rw [b3Rest_SF.inner_def, b3Rest_inner, b3Rest_SF.form_mk, b3Forms_star_star,
    show -η = (-1 : ℝ) • η from (neg_one_smul ℝ η).symm, b3Rest_wedgeForm_smul,
    b3Forms_integral_smul]
  ring

/-- **The star of a dual form is orthogonal to the closure of the exact forms.** -/
theorem b3Rest_inner_Ex_star_dual {P : ℝ → C} (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P)
    (hper : Function.Periodic P 1) {η : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hη : b3Forms_IsSmooth η)
    (hη' : ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
      b3Forms_integral (b3Rest_b hE1.out) (b3Forms_wedgeForm α η) = b3Forms_lineIntegral α P 0 1)
    {y : b3Rest_L2 E C} (hy : y ∈ b3Rest_Ex E C) :
    inner ℝ y ((b3Rest_SF.mk (b3Forms_star η) hη.star : b3Rest_SF E C) : b3Rest_L2 E C) = 0 := by
  refine b3Rest_inner_closure_eq_zero ?_ hy
  rintro _ ⟨g, rfl⟩
  rw [UniformSpace.Completion.inner_coe, b3Rest_inner_star_eq _ hη]
  show -b3Forms_integral (b3Rest_b hE1.out)
    (b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g.1)) η) = 0
  rw [hη' _ g.2.d (b3Forms_d_d g.2), b3Forms_lineIntegral_d g.2 hP]
  have : P 1 = P 0 := by simpa using hper 0
  rw [this, sub_self, neg_zero]

/-- **A smooth closed form in the closure of the exact forms has vanishing periods.** -/
theorem b3Rest_periodsVanish_of_mem_Ex {e : b3Rest_SF E C} (hde : b3Forms_d e.form = 0)
    (he : (e : b3Rest_L2 E C) ∈ b3Rest_Ex E C) : b3Forms_PeriodsVanish e.form := by
  intro P hper hP
  obtain ⟨η, hη, hη'⟩ := b3Rest_exists_dual hE1.out hP hper
  have h0 := b3Rest_inner_Ex_star_dual hP hper hη hη' he
  rw [UniformSpace.Completion.inner_coe, b3Rest_inner_star_eq _ hη, hη' e.form e.isSmooth hde] at h0
  linarith

variable [ConnectedSpace C]

/-- **Hodge decomposition of closed `1`-forms**: every smooth closed real `1`-form on a compact
Riemann surface is `Re θ + dg` for a holomorphic form `θ` and a smooth function `g`. -/
theorem b3Rest_hodge {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hdα : b3Forms_d α = 0) :
    ∃ θ : b3_HolForm E C, ∃ g : C → ℝ, b3Forms_IsSmooth (b3Forms_fun (E := E) g) ∧
      α = b3Forms_reForm θ + b3Forms_d (b3Forms_fun (E := E) g) := by
  set a : b3Rest_SF E C := b3Rest_SF.mk α hα
  obtain ⟨e, he, h1, h2⟩ := b3Rest_decomp (α := a) hdα
  obtain ⟨β, hdβ, hdsβ, hβ⟩ := b3Rest_weakHarmonic_eq _ h1 h2
  set e' : b3Rest_SF E C := a - β
  have he' : ((e' : b3Rest_SF E C) : b3Rest_L2 E C) = e := by
    rw [UniformSpace.Completion.coe_sub, ← hβ]
    abel
  have hde' : b3Forms_d e'.form = 0 := by
    rw [b3Rest_SF.form_sub, sub_eq_add_neg, ← neg_one_smul ℝ β.form,
      b3Forms_d_add a.isSmooth (β.isSmooth.smul _), b3Forms_d_smul, hdβ]
    simpa [a] using hdα
  obtain ⟨g, hg, hdg⟩ := b3Forms_exists_primitive e'.isSmooth hde'
    (b3Rest_periodsVanish_of_mem_Ex hde' (he' ▸ he))
  refine ⟨b3Forms_harmonicHol hE1.out ⟨β.isSmooth, hdβ, hdsβ⟩, g, hg, ?_⟩
  have hre := b3Forms_reForm_harmonicHol hE1.out
    (⟨β.isSmooth, hdβ, hdsβ⟩ : b3Forms_IsHarmonic β.form)
  erw [hre, hdg, b3Rest_SF.form_sub]
  simp [a]
end HodgeLean.Foundations.Program
