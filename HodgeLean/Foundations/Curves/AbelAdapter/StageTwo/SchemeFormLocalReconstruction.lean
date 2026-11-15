import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ChartFormTransport
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormRelations

/-! # Local scheme representatives of B3 one-forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The actual open source of a specified complex-point chart.
Source: Griffiths–Harris, chapter 0 §2; extChartAt_source.
HC no distance; AV milestone no distance. -/
def schemeChartSource (z : ComplexPoint X) : Opens (TopCat.of (ComplexPoint X)) :=
  ⟨(extChartAt 𝓘(ℂ, Fin d → ℂ) z).source, isOpen_extChartAt_source z⟩

/-- A raw local scheme form realizing the original B3 form in the specified chart.
Source: Griffiths–Harris, chapter 0 §2; formOfAnalyticField.
HC no distance; AV milestone no distance. -/
def localB3Form (θ : b3_HolForm (Fin d → ℂ) (ComplexPoint X)) (z : ComplexPoint X) :
    Algebra.DeRham.Form ℂ
      (OpenHolomorphicFunctions X d (op (schemeChartSource X d z))) 1 :=
  formOfAnalyticField X d (op (schemeChartSource X d z)) z (fun _ hx ↦ hx) 1
    (b3ChartField θ z)
    ((b3ChartField_analyticOnNhd θ z).mono (by
      intro y hy
      have hy' := hy.1
      rw [extChartAt_target] at hy'
      exact hy'.1))

/-- The local representative retains exactly the original alternating field in its fixed chart.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluation_formOfAnalyticField.
HC no distance; AV milestone no distance. -/
theorem localB3Form_fixed_values (θ : b3_HolForm (Fin d → ℂ) (ComplexPoint X))
    (z : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d (op (schemeChartSource X d z)) z) :
    chartEvaluation X d (op (schemeChartSource X d z)) z 1 (localB3Form X d θ z) y =
      b3ChartField θ z y :=
  chartEvaluation_formOfAnalyticField X d (op (schemeChartSource X d z)) z
    (fun _ hx ↦ hx) 1 (b3ChartField θ z) _ hy

/-- The local scheme representative retains every original tangent value on its chart source.
Source: Griffiths–Harris, chapter 0 §2; chartEvaluation_fixedChartTransition.
HC no distance; AV milestone no distance. -/
theorem localB3Form_tangent_values (θ : b3_HolForm (Fin d → ℂ) (ComplexPoint X))
    (z : ComplexPoint X) (v : TangentBundle 𝓘(ℂ, Fin d → ℂ) (ComplexPoint X))
    (hv : v.1 ∈ schemeChartSource X d z) :
    localFormValues X d (schemeChartSource X d z) (localB3Form X d θ z) v = θ.val v := by
  have hsrc : v.1 ∈ (chartAt (Fin d → ℂ) z).source := by
    change v.1 ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source at hv
    rwa [extChartAt_source] at hv
  have hself : (extChartAt 𝓘(ℂ, Fin d → ℂ) v.1).symm
      (extChartAt 𝓘(ℂ, Fin d → ℂ) v.1 v.1) ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source := by
    rw [extChartAt_to_inv]
    exact hv
  change chartEvaluation X d (op (schemeChartSource X d z)) v.1 1
    (localB3Form X d θ z) (extChartAt 𝓘(ℂ, Fin d → ℂ) v.1 v.1) (fun _ ↦ v.2) = _
  rw [chartEvaluation_fixedChartTransition X d (op (schemeChartSource X d z)) z v.1 1
    (localB3Form X d θ z)
    (extChartAt_self_mem_chartSectionDomain X d (op (schemeChartSource X d z)) hv) hself]
  have hcoord : fixedChartTransition X d z v.1 (extChartAt 𝓘(ℂ, Fin d → ℂ) v.1 v.1) =
      extChartAt 𝓘(ℂ, Fin d → ℂ) z v.1 := by
    unfold fixedChartTransition
    rw [extChartAt_to_inv]
  have hy : extChartAt 𝓘(ℂ, Fin d → ℂ) z v.1 ∈
      chartSectionDomain X d (op (schemeChartSource X d z)) z := by
    refine ⟨(extChartAt 𝓘(ℂ, Fin d → ℂ) z).map_source hv, ?_⟩
    change (extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm
      (extChartAt 𝓘(ℂ, Fin d → ℂ) z v.1) ∈ schemeChartSource X d z
    rw [(extChartAt 𝓘(ℂ, Fin d → ℂ) z).left_inv hv]
    exact hv
  rw [hcoord, localB3Form_fixed_values X d θ z hy]
  change b3ChartCovector θ z (chartAt (Fin d → ℂ) z v.1)
    (fderiv ℂ (b3Forms_tr v.1 z) (chartAt (Fin d → ℂ) v.1 v.1) v.2) = θ.val v
  exact b3ChartCovector_transport θ z v.1 hsrc v.2

#print axioms localB3Form
#print axioms localB3Form_fixed_values
#print axioms localB3Form_tangent_values

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
