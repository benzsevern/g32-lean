import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveImage

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
namespace HodgeLean.Foundations.Program

/-- A closed carrier is determined by its complex points over ℂ.
Source: the Jacobson property of schemes locally of finite type over a field. -/
theorem s0_carrier_eq_closure_range
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {C : Type} (f : C → ComplexPoint X) (Z : Set X.left) (hZ : IsClosed Z)
    (hcar : range f = (Point.underlying : ComplexPoint X → X.left) ⁻¹' Z) :
    Z = closure (range (fun x ↦ (f x).underlying)) := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply le_antisymm
  · rw [← closure_inter_closedPoints hZ]
    apply closure_mono
    intro z hz
    let a : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom z hz.2) (pointOfClosedPoint_comp X.hom z hz.2)
    have ha : a.underlying = z := pointOfClosedPoint_apply X.hom z hz.2 _
    have haZ : a ∈ range f := by
      rw [hcar]
      change a.underlying ∈ Z
      rw [ha]
      exact hz.1
    obtain ⟨x, hx⟩ := haZ
    exact ⟨x, (congrArg Point.underlying hx).trans ha⟩
  · apply closure_minimal _ hZ
    rintro _ ⟨x, rfl⟩
    exact (show f x ∈ (Point.underlying : ComplexPoint X → X.left) ⁻¹' Z from
      hcar ▸ mem_range_self x)

#print axioms s0_carrier_eq_closure_range
end HodgeLean.Foundations.Program
