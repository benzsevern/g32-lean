import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.Foundations.Analytic.Analytification
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Original holomorphic coordinates on smooth complex schemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.QuotientDuality

/-- Every coordinate of the original algebraic smooth chart is holomorphic for the actual analytification structure sheaf.
Source: SGA 1, Expose XII, Proposition 3.1; f4_isHolFun_iff_contMDiffOn.
HC no distance; AV milestone no distance. -/
lemma properCycle_smooth_local_chart_holomorphic
    (V : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d V.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (x : ComplexPoint V) :
    ∀ i, (f4_analytification V).IsHolFun
      (fun z : (ComplexPoint.localChart V d x).source => ComplexPoint.localChart V d x z i) := by
  intro i
  apply (f4_isHolFun_iff_contMDiffOn V d
    (fun z => ComplexPoint.localChart V d x z i) (ComplexPoint.localChart V d x).open_source).2
  have hchart : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (ComplexPoint.localChart V d x) (ComplexPoint.localChart V d x).source :=
    contMDiffOn_chart
  exact (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).contMDiff.comp_contMDiffOn hchart

end HodgeLean.Foundations.QuotientDuality
