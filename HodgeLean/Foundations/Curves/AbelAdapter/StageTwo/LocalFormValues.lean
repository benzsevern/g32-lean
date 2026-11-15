import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormSmoothness

/-! # Tangent values of local representatives

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The tangent values of raw local one-forms, evaluated in the chart at each point.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluationAt.
HC no distance; AV milestone no distance. -/
def localFormValues (U : Opens (TopCat.of (ComplexPoint X))) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) 1 →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X) → ℂ) where
  toFun θ v := chartEvaluationAt X d (op U) v.1 1
    (extChartAt 𝓘(ℂ, Fin d → ℂ) v.1 v.1) θ (fun _ ↦ v.2)
  map_add' a b := by
    funext v
    exact congrArg (fun θ ↦ θ (fun _ ↦ v.2))
      ((chartEvaluationAt X d (op U) v.1 1 _).map_add a b)
  map_smul' c a := by
    funext v
    exact congrArg (fun θ ↦ θ (fun _ ↦ v.2))
      ((chartEvaluationAt X d (op U) v.1 1 _).map_smul c a)

/-- The tangent value of a generator is its coefficient times the tangent differential.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluation_mk.
HC no distance; AV milestone no distance. -/
theorem localFormValues_mk (U : Opens (TopCat.of (ComplexPoint X)))
    (a : OpenHolomorphicFunctions X d (op U))
    (f : Fin 1 → OpenHolomorphicFunctions X d (op U))
    (v : TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X)) (hv : v.1 ∈ U) :
    localFormValues X d U (Algebra.DeRham.mk ℂ _ 1 a f) v =
      extendedSection X d (op U) a v.1 *
        tangentSpaceCastModel 𝓘(ℂ, ℂ) (extendedSection X d (op U) (f 0) v.1)
          (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ)
            (extendedSection X d (op U) (f 0)) v.1 v.2) := by
  change chartOneFormCovector X d (op U) v.1
    (Algebra.DeRham.mk ℂ _ 1 a f) (extChartAt 𝓘(ℂ, Fin d → ℂ) v.1 v.1) v.2 = _
  rw [chartOneFormCovector_mk X d (op U) v.1 a f
    (extChartAt_self_mem_chartSectionDomain X d (op U) hv)]
  rw [localSection_mfderiv X d U (f 0) hv]
  change extendedSection X d (op U) a
    ((extChartAt 𝓘(ℂ, Fin d → ℂ) v.1).symm (extChartAt 𝓘(ℂ, Fin d → ℂ) v.1 v.1)) * _ = _
  rw [extChartAt_to_inv]
  rfl

/-- Every local raw one-form has holomorphic tangent values on its open set.
Source: Griffiths–Harris, chapter 0 §2; Algebra.DeRham.mk_induction.
HC no distance; AV milestone no distance. -/
theorem localFormValues_contMDiffOn (U : Opens (TopCat.of (ComplexPoint X)))
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) 1) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ).tangent 𝓘(ℂ, ℂ) ω
      (localFormValues X d U θ) {v | v.1 ∈ U} := by
  induction θ using Algebra.DeRham.mk_induction with
  | mk a f =>
      have ha : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω
          (extendedSection X d (op U) a) (U : Set (ComplexPoint X)) :=
        fun x hx ↦ (localSection_contMDiffAt X d U a hx).contMDiffWithinAt
      have hp : ContMDiffOn 𝓘(ℂ, Fin d → ℂ).tangent 𝓘(ℂ, ℂ) ω
          (fun v : TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X) ↦
            extendedSection X d (op U) a v.1) {v | v.1 ∈ U} :=
        ha.comp (Bundle.contMDiffOn_proj (TangentSpace 𝓘(ℂ, Fin d → ℂ))) (fun _ hv ↦ hv)
      have hd := localSection_tangentDerivative X d U (f 0)
      exact (hp.mul hd).congr fun v hv ↦ localFormValues_mk X d U a f v hv
  | zero =>
      rw [map_zero]
      exact contMDiffOn_const
  | add a b ha hb =>
      rw [map_add]
      exact ha.add hb
  | smul c a ha =>
      rw [map_smul]
      exact ((contMDiffOn_const (c := c)).mul ha).congr fun v _ ↦ smul_eq_mul c _

#print axioms localFormValues
#print axioms localFormValues_mk
#print axioms localFormValues_contMDiffOn

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
