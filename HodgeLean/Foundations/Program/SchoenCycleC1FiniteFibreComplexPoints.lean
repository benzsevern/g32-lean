import HodgeLean.Foundations.Program.SchoenCycleComplexPointStabilizer
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Actual complex representatives of finite geometric fibres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Every scheme point in the finite fibre of a specified complex point has
a complex representative in that same actual fibre. -/
theorem s2e_c1_finite_fibre_complex_representative
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (y : ComplexPoint Y)
    (x : X.left) (hx : f.left x = y.underlying) :
    ∃ z : ComplexPoint X, z.underlying = x ∧ Point.map f z = y := by
  have hy : IsClosed ({y.underlying} : Set Y.left) :=
    ((pointEquivClosedPoint Y.hom) ⟨y.left, by simp⟩).2
  have hc : IsClosed ({x} : Set X.left) := isClosed_of_subset_discrete_closed
    (Set.singleton_subset_iff.mpr hx) (f.left.isDiscrete_preimage_singleton y.underlying)
    (hy.preimage f.left.continuous)
  let z : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hc)
    (pointOfClosedPoint_comp X.hom x hc)
  have hz : z.underlying = x := pointOfClosedPoint_apply X.hom x hc _
  refine ⟨z, hz, ?_⟩
  apply underlying_injective_of_locallyOfFiniteType
  rw [Point.underlying_map, hz, hx]

end HodgeLean.Foundations.Program
