import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily

/-! # Regular coordinates of the native curve charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Each native curve chart coordinate is an actual regular section evaluation
on the specified algebraic coordinate neighbourhood.
Source: HodgeConjecture, `localChart_apply_of_mem` and
`LocalEtaleCoordinates.ambientAnalyticCoordinates_apply_eq_evaluate`. -/
theorem s2e_u1_native_chart_regular_coordinate
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    (p x : ComplexPoint Z) (hx : x ∈ (localChart Z 1 p).source) :
    localChart Z 1 p x 0 =
      Point.evaluate (localEtaleCoordinates Z 1 p).ambientCoordinateOpen
        ((localEtaleCoordinates Z 1 p).ambientCoordinateSection 0) x := by
  rw [localChart_apply_of_mem Z 1 p x hx]
  exact (localEtaleCoordinates Z 1 p).ambientAnalyticCoordinates_apply_eq_evaluate _ 0

/-- On an inverse native chart, evaluation of its regular coordinate is exactly
the chart parameter, so collisions do not require a coordinate approximation.
Source: HodgeConjecture, `localChart_apply_of_mem`; Mathlib,
`OpenPartialHomeomorph.right_inv`. -/
theorem s2e_u1_native_inverse_chart_regular_coordinate
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom]
    (p : ComplexPoint Z) (w : Fin 1 → ℂ) (hw : w ∈ (localChart Z 1 p).target) :
    Point.evaluate (localEtaleCoordinates Z 1 p).ambientCoordinateOpen
      ((localEtaleCoordinates Z 1 p).ambientCoordinateSection 0)
      ((localChart Z 1 p).symm w) = w 0 := by
  rw [← s2e_u1_native_chart_regular_coordinate Z p _ ((localChart Z 1 p).map_target hw),
    (localChart Z 1 p).right_inv hw]

end HodgeLean.Foundations.Program
