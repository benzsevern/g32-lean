import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormValues

/-! # Local form relations detected by tangent values

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Vanishing tangent values detect the local relations defining holomorphic one-forms.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluation_fixedChartTransition.
HC no distance; AV milestone no distance. -/
theorem rawForm_mem_kernel_of_tangentValues_zero (U : Opens (TopCat.of (ComplexPoint X)))
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) 1)
    (h : ∀ v : TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X),
      v.1 ∈ U → localFormValues X d U θ v = 0) :
    θ ∈ chartEvaluationKernel X d (op U) 1 := by
  apply (mem_chartEvaluationKernel_iff X d (op U) 1 θ).mpr
  intro z y hy
  let x := (extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y
  have hx : x ∈ U := hy.2
  have hz : chartEvaluation X d (op U) x 1 θ (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) = 0 := by
    ext v
    have hv := h ⟨x, v 0⟩ hx
    change chartEvaluation X d (op U) x 1 θ (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)
      (fun _ ↦ v 0) = 0 at hv
    have he : (fun _ : Fin 1 ↦ v 0) = v := by
      funext i
      exact congrArg v (Subsingleton.elim _ _)
    rw [he] at hv
    exact hv
  rw [chartEvaluation_fixedChartTransition X d (op U) x z 1 θ hy
    (show x ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) x).source from mem_extChartAt_source x)]
  change (chartEvaluation X d (op U) x 1 θ (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)).compContinuousLinearMap _ = 0
  rw [hz]
  ext v
  rfl

#print axioms rawForm_mem_kernel_of_tangentValues_zero

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
