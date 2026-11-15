import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LocalFormCoefficients
import HodgeLean.Foundations.Program.CurveJacobianFormsHol

/-! # Analytic fields representing B3 one-forms in a fixed chart

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

/-- The covector field of a B3 form in one fixed chart.
Source: Forster, §9; b3Forms_chartVec and b3Forms_holCLM.
HC no distance; AV milestone no distance. -/
def b3ChartCovector (θ : b3_HolForm E C) (z : C) (y : E) : E →L[ℂ] ℂ :=
  (b3Forms_holCLM θ ((chartAt E z).symm y)).comp
    (fderiv ℂ (b3Forms_tr z ((chartAt E z).symm y)) y)

/-- The fixed-chart covector field is holomorphic on the chart target.
Source: Forster, §9; b3Forms_contMDiffOn_chartVec.
HC no distance; AV milestone no distance. -/
theorem b3ChartCovector_contDiffOn (θ : b3_HolForm E C) (z : C) :
    ContDiffOn ℂ ω (b3ChartCovector θ z) (chartAt E z).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  exact (θ.2.1.comp_contMDiffOn (b3Forms_contMDiffOn_chartVec z v)).contDiffOn

/-- The one-alternating-form field of a B3 form in a fixed chart.
Source: Forster, §9; ContinuousAlternatingMap.ofSubsingletonLIE.
HC no distance; AV milestone no distance. -/
def b3ChartField (θ : b3_HolForm E C) (z : C) (y : E) : E [⋀^Fin 1]→L[ℂ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ) (0 : Fin 1)) (b3ChartCovector θ z y)

/-- The fixed-chart alternating field has analytic coefficients on the chart target.
Source: Forster, §9; b3Forms_contMDiffOn_chartVec.
HC no distance; AV milestone no distance. -/
theorem b3ChartField_analyticOnNhd (θ : b3_HolForm E C) (z : C) :
    AnalyticOnNhd ℂ (b3ChartField θ z) (chartAt E z).target := by
  have h : ContDiffOn ℂ ω (b3ChartField θ z) (chartAt E z).target :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (b3ChartCovector_contDiffOn θ z)
  exact (chartAt E z).open_target.analyticOn_iff_analyticOnNhd.mp h.analyticOn

#print axioms b3ChartCovector_contDiffOn
#print axioms b3ChartField_analyticOnNhd

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
