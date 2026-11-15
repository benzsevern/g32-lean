import HodgeLean.Foundations.Program.G32Native.ChartDerivativeIdentities

/-! # Tangent coordinate changes in the original ambient charts -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Tangent coordinates from the point chart to a specified fixed chart.
Source: Lee, Introduction to Smooth Manifolds, 2nd ed., ch. 10, chart transitions. -/
def pointToFixedTangent (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p y : ComplexPoint W) :
    (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
  fderiv ℂ (fun u => localChart W d p ((localChart W d y).symm u)) (localChart W d y y)

/-- Tangent coordinates from a specified fixed chart to the point chart.
Source: Lee, Introduction to Smooth Manifolds, 2nd ed., ch. 10, chart transitions. -/
def fixedToPointTangent (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p y : ComplexPoint W) :
    (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
  fderiv ℂ (fun u => localChart W d y ((localChart W d p).symm u)) (localChart W d p y)

/-- The original tangent changes are inverse on the fixed chart overlap. -/
theorem pointToFixed_comp_fixedToPoint (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p y : ComplexPoint W)
    (hy : y ∈ (localChart W d p).source) :
    (pointToFixedTangent W d p y).comp (fixedToPointTangent W d p y) =
      ContinuousLinearMap.id ℂ (Fin d → ℂ) := by
  exact localChart_transition_fderiv_comp W d y p y (mem_localChart_source W d y) hy

#print axioms pointToFixedTangent
#print axioms fixedToPointTangent
#print axioms pointToFixed_comp_fixedToPoint
end HodgeLean.Foundations.Program.G32Native
