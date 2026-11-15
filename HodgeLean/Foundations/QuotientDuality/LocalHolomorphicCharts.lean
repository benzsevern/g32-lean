import HodgeLean.Foundations.Analytic.Analytification
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

/-! The canonical algebraic smooth chart has holomorphic coordinate functions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem localChart_coordinates_holomorphic (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (x : ComplexPoint X) (j : Fin d) :
    (f4_analytification X).IsHolFun
      (fun y : (localChart X d x).source => localChart X d x y j) := by
  let D := localEtaleCoordinates X d x
  have hs : (localChart X d x).source ⊆ (Point.overOpen D.ambientCoordinateOpen : Set (ComplexPoint X)) := by
    intro y hy
    have hm := mem_coordinateNeighborhood_of_mem_localChart_source X d x y hy
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hm
  have hh := anrem_isHolFun_restrict (f4_analytification X) hs
    (f4_isHolFun_evaluate X D.ambientCoordinateOpen (D.ambientCoordinateSection j))
  have heq : (fun y : (localChart X d x).source => localChart X d x y j) =
      (fun y : (localChart X d x).source =>
        Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection j) y.val) := by
    funext y
    exact localChart_apply_component_eq_evaluate X d x y.val y.property j
  rw [heq]
  exact hh

#print axioms localChart_coordinates_holomorphic
end HodgeLean.Foundations.QuotientDuality
