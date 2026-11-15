import HodgeLean.Foundations.Program.SchoenCycleParameterPullback
import HodgeLean.Foundations.Program.SchoenCycleCurveParameterResidue

/-! # Actual regular parameters under constant maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback of the actual parameter along its own complex point is zero at
every complex base point.
Source: Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_curvePullbackParameter_point_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X)
    (z : ComplexPoint (Over.mk (𝟙 (Spec ↧ℂ)))) :
    s2e_curvePullbackParameter X (Over.mk (𝟙 (Spec ↧ℂ))) p z = 0 := by
  have hz : z = 𝟙 (Over.mk (𝟙 (Spec ↧ℂ))) := by
    apply Over.OverMorphism.ext
    change z.left = 𝟙 (Spec ↧ℂ)
    have hw : z.left ≫ 𝟙 (Spec ↧ℂ) = 𝟙 (Spec ↧ℂ) := Over.w z
    exact (Category.comp_id z.left).symm.trans hw
  subst z
  change p.left.stalkMap (IsLocalRing.closedPoint ℂ)
    (s2e_curvePointParameter X (𝟙 (Over.mk (𝟙 (Spec ↧ℂ))) ≫ p)) = 0
  have h := s2e_curvePointParameter_point_stalkMap_zero X
    ((𝟙 (Over.mk (𝟙 (Spec ↧ℂ)))) ≫ p)
  change ((𝟙 (Spec ↧ℂ)) ≫ p.left).stalkMap (IsLocalRing.closedPoint ℂ)
    (s2e_curvePointParameter X ((𝟙 (Over.mk (𝟙 (Spec ↧ℂ)))) ≫ p)) = 0 at h
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_id] at h
  change ((p.left.stalkMap (IsLocalRing.closedPoint ℂ)) ≫ 𝟙 _).hom
    (s2e_curvePointParameter X ((𝟙 (Over.mk (𝟙 (Spec ↧ℂ)))) ≫ p)) = 0 at h
  rw [Category.comp_id] at h
  exact h

/-- A morphism factoring through the chosen complex point kills the native
regular parameter at its image.
Source: Hartshorne, Algebraic Geometry, II.2, composition of stalk maps. -/
theorem s2e_curvePullbackParameter_constant_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (Y : Over (Spec ↧ℂ)) (f : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ)))
    (p : ComplexPoint X) (y : ComplexPoint Y) :
    s2e_curvePullbackParameter X Y (f ≫ p) y = 0 := by
  rw [← s2e_curvePullbackParameter_comp X Y (Over.mk (𝟙 (Spec ↧ℂ))) f p y,
    s2e_curvePullbackParameter_point_zero, map_zero]

end HodgeLean.Foundations.Program
