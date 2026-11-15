import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexFibers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
namespace HodgeLean.Foundations.Program

/-- Surjectivity on complex points gives dominance over a target locally of finite type.
Source: density of closed points on schemes of finite type over an algebraically closed field. -/
theorem s0_dominant_of_surjective_complex_points
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (hf : Function.Surjective (Point.map f)) : IsDominant f.left := by
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hs : closedPoints Y.left ⊆ Set.range f.left := by
    intro y hy
    let b : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy)
      (pointOfClosedPoint_comp Y.hom y hy)
    have hb : b.underlying = y := pointOfClosedPoint_apply Y.hom y hy _
    obtain ⟨a, ha⟩ := hf b
    refine ⟨a.underlying, ?_⟩
    exact (congrArg Point.underlying ha).trans hb
  rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← closure_closedPoints (X := Y.left)]
  exact closure_mono hs

#print axioms s0_dominant_of_surjective_complex_points
end HodgeLean.Foundations.Program
