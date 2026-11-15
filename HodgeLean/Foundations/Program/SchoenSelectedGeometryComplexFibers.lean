import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteMorphism

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Finite analytic fibres detect finiteness of a proper complex algebraic morphism.
Source: closed points over an algebraically closed field and the proper quasi-finite criterion. -/
theorem s0_finite_of_finite_complex_fibers
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hfib : ∀ y : ComplexPoint Y, ((Point.map f) ⁻¹' {y}).Finite) : IsFinite f.left := by
  apply s0_finite_of_finite_closed_fibers X.hom Y.hom f.left
  intro y hy
  let b : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy)
    (pointOfClosedPoint_comp Y.hom y hy)
  have hb : b.underlying = y := pointOfClosedPoint_apply Y.hom y hy _
  apply ((hfib b).image (Point.underlying : ComplexPoint X → X.left)).subset
  intro x hx
  let a : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hx.2)
    (pointOfClosedPoint_comp X.hom x hx.2)
  have ha : a.underlying = x := pointOfClosedPoint_apply X.hom x hx.2 _
  refine ⟨a, ?_, ha⟩
  change Point.map f a = b
  apply underlying_injective_of_locallyOfFiniteType
  change f.left a.underlying = b.underlying
  rw [ha, hb]
  exact hx.1

#print axioms s0_finite_of_finite_complex_fibers
end HodgeLean.Foundations.Program
