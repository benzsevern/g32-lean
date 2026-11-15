import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.FormCoordinates

/-! # Holomorphic coefficients of local scheme one-forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The covector coefficient of a local one-form in a fixed chart.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluation.
HC no distance; AV milestone no distance. -/
def chartOneFormCovector (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 1)
    (y : Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
    (chartEvaluation X d U z 1 θ y)

/-- The coefficient of a generator is its scalar coefficient times the coordinate derivative.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluation_mk.
HC no distance; AV milestone no distance. -/
theorem chartOneFormCovector_mk (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (a : OpenHolomorphicFunctions X d U)
    (f : Fin 1 → OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartOneFormCovector X d U z (Algebra.DeRham.mk ℂ _ 1 a f) y =
      chartSection X d U z a y • chartSectionDifferential X d U z (f 0) y := by
  ext v
  change chartEvaluation X d U z 1 (Algebra.DeRham.mk ℂ _ 1 a f) y (fun _ ↦ v) = _
  rw [chartEvaluation_mk X d U z 1 a f hy]
  simp only [chartGeneratorEvaluation, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.wedgeCovectors_apply_eq_det, Matrix.det_unique,
    Matrix.of_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

/-- A holomorphic section extended by zero is holomorphic at every point of its open.
Source: Griffiths–Harris, chapter 0 §2; holomorphicFunctionSheaf_section_analytic.
HC no distance; AV milestone no distance. -/
theorem localSection_contMDiffAt (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) {x : ComplexPoint X} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (extendedSection X d (op U) f) x := by
  apply (contMDiffAt_subtype_iff (U := (U : Opens (ComplexPoint X)))
    (x := ⟨x, hx⟩)).mp
  simpa only [extendedSection, Subtype.val_injective.extend_apply] using
    (holomorphicFunctionSheaf_section_analytic X d f).contMDiffAt (x := ⟨x, hx⟩)

/-- The tangent derivative of a local function is its literal chart differential.
Source: Griffiths–Harris, chapter 0 §2; MDifferentiableAt.mfderiv.
HC no distance; AV milestone no distance. -/
theorem localSection_mfderiv (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (op U)) {x : ComplexPoint X} (hx : x ∈ U) :
    mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (extendedSection X d (op U) f) x =
      chartSectionDifferential X d (op U) x f (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
  rw [((localSection_contMDiffAt X d U f hx).mdifferentiableAt (by simp)).mfderiv,
    chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d (op U) x)
      (extChartAt_self_mem_chartSectionDomain X d (op U) hx)]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, Function.id_comp]
  rfl

#print axioms chartOneFormCovector_mk
#print axioms localSection_contMDiffAt
#print axioms localSection_mfderiv

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
