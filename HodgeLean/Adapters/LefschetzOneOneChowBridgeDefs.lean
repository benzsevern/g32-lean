import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianDefs
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24CurveExamples

/-! # Concrete divisor inputs for the Chow bridge

The fixed cubic carries the identity-point divisor and the empty divisor.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic24
open Filter Set Topology
namespace HodgeLean.Adapters

/-- The identity-point divisor on the fixed smooth projective cubic.
Source: gaga24_curve_data, gaga24_curve_periodic, and gaga24_curve_image. -/
def bhg_curveDivisor : bh4_LocalDivisorData Curves.E where
  ι := Option gaga24_Lattice
  V := gaga24_curveOpen
  f := gaga24_curveEquation
  valid := gaga24_curve_data
  periodic := gaga24_curve_periodic

example : abelianExp Curves.E '' localDivisorSupport bhg_curveDivisor.V
    bhg_curveDivisor.f = {abelianExp Curves.E 0} := gaga24_curve_image

/-- Unit local equations construct the empty effective divisor in every dimension.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §1 (divisors). -/
def bhg_emptyDivisor (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] : bh4_LocalDivisorData X where
  ι := Unit
  V := fun _ ↦ univ
  f := fun _ _ ↦ 1
  valid := by
    refine ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ analyticOnNhd_const, ?_, ?_⟩
    · intro _ p _ h
      exact one_ne_zero h.self_of_nhds
    · intro _ _ p _
      exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
        Eventually.of_forall fun _ ↦ by simp⟩
  periodic := by
    intro l i j p hi hj
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
      Eventually.of_forall fun _ ↦ by simp⟩

example : localDivisorSupport (bhg_emptyDivisor Curves.E).V
    (bhg_emptyDivisor Curves.E).f = ∅ := by
  simp [bhg_emptyDivisor, localDivisorSupport]

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    bh4_Algebraization X (bhg_emptyDivisor X) := by
  refine ⟨0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0,
    Fin.elim0, fun i ↦ i.elim0, ?_, ?_⟩
  · simp [bhg_emptyDivisor, localDivisorSupport]
  · intro j p hp
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
      Eventually.of_forall fun z ↦ by simp [bhg_emptyDivisor]⟩

end HodgeLean.Adapters
