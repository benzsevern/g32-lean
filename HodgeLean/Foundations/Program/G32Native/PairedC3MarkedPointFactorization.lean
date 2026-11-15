import HodgeLean.Foundations.Program.G32Native.PairedC3InitialFibreFactor

/-! # Factorization retaining a specified map on complex points -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Factor through the given immersion while retaining the supplied point map.
The point map can carry the projectivization of the original linear injection.
Source: Hartshorne, Algebraic Geometry, II.3, reduced closed subschemes. -/
theorem paired_c3_factor_closed_immersion_with_point_map
    (X Y Z : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [IsReduced X.left] [IsReduced Y.left]
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion g.left]
    (q : ComplexPoint X → ComplexPoint Y)
    (hq : ∀ p, Point.map g (q p) = Point.map f p) :
    ∃ i : X ⟶ Y, i ≫ g = f ∧ Point.map i = q := by
  obtain ⟨i, hi⟩ := paired_c3_factor_closed_immersion_of_point_image X Y Z f g
    (fun p => ⟨q p, hq p⟩)
  refine ⟨i, hi, ?_⟩
  funext p
  haveI : Mono g := Over.mono_of_mono_left g
  apply ComplexPoint.map_injective_of_mono g
  rw [← Point.map_comp_apply, hi]
  exact (hq p).symm

#print axioms paired_c3_factor_closed_immersion_with_point_map

end HodgeLean.Foundations.Program.G32Native
