import HodgeLean.Foundations.Program.SchoenCycleCurveParameters

/-! # Pullback of consistently chosen actual curve parameters -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pull back the chosen curve parameter at the image of an actual point.
Source: Hartshorne, Algebraic Geometry, II.2, maps on stalks. -/
def s2e_curvePullbackParameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (Y : Over (Spec ↧ℂ)) (f : Y ⟶ X) (y : ComplexPoint Y) :
    Y.left.presheaf.stalk y.underlying :=
  f.left.stalkMap y.underlying (s2e_curvePointParameter X (Point.map f y))

/-- Pullback of the point-indexed parameter commutes with composition of
actual scheme morphisms.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of stalk maps. -/
theorem s2e_curvePullbackParameter_comp
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (Y Z : Over (Spec ↧ℂ)) (f : Y ⟶ Z) (g : Z ⟶ X) (y : ComplexPoint Y) :
    f.left.stalkMap y.underlying (s2e_curvePullbackParameter X Z g (Point.map f y)) =
      s2e_curvePullbackParameter X Y (f ≫ g) y := by
  dsimp only [s2e_curvePullbackParameter]
  change (f.left.stalkMap y.underlying).hom
      ((g.left.stalkMap (f.left y.underlying)).hom _) =
    ((f.left ≫ g.left).stalkMap y.underlying).hom _
  rw [Scheme.Hom.stalkMap_comp]
  rfl

end HodgeLean.Foundations.Program
