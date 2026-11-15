import Mathlib.Analysis.Complex.Polynomial.Basic
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualCoverTopology
import HodgeLean.Foundations.Program.SchoenCycleClosedPointDetection
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic

/-! # Residual base coverage from complex-point neighbourhoods -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Affine neighbourhoods covering the complex points of the residual base
cover its whole scheme support. No assumption on the other ambient points
is needed.
Source: Hartshorne, Algebraic Geometry, II.3. -/
theorem pairedC3_residual_base_cover_of_complex_points
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (D : TopologicalSpace.Closeds X.left) {ι : Type*} (U : ι → X.left.Opens)
    (h : ∀ p : ComplexPoint X, p.underlying ∈ D → ∃ i, p.underlying ∈ U i) :
    (D : Set X.left) ⊆ ⋃ i, (U i : Set X.left) := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply pairedC3_closed_subset_iUnion_of_closed_points D.isClosed _ (fun i => (U i).isOpen)
  intro x hx hc
  let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hc)
    (pointOfClosedPoint_comp X.hom x hc)
  have hp : p.underlying = x := pointOfClosedPoint_apply X.hom x hc _
  obtain ⟨i, hi⟩ := h p (hp.symm ▸ hx)
  refine ⟨i, ?_⟩
  change x ∈ U i
  exact hp ▸ hi

#print axioms pairedC3_residual_base_cover_of_complex_points
end HodgeLean.Foundations.Program.G32Native
