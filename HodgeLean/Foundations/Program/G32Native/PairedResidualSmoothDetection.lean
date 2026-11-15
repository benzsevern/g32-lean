import HodgeLean.Foundations.Program.SchoenCycleClosedPointDetection
import HodgeLean.Foundations.Program.SchoenCycleSectionEvaluation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Detecting smoothness of the actual residual family at complex points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The smooth locus of a finitely presented morphism contains the entire
source if it contains every complex point of that source.
Source: EGA IV, 17.3.3; Hartshorne, Algebraic Geometry, II.3. -/
theorem residual_smooth_of_complex_points
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left]
    (h : ∀ p : ComplexPoint X, p.underlying ∈ f.left.smoothLocus) :
    Smooth f.left := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply s2e_open_eq_top_of_contains_closed_points
  intro x hc
  let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hc) (by simp)
  have hp : p.underlying = x := pointOfClosedPoint_apply X.hom x hc _
  simpa only [hp] using h p

#print axioms residual_smooth_of_complex_points
end HodgeLean.Foundations.Program.G32Native
