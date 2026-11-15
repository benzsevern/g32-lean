import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientPointRestriction
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A literal integral-chart point square retains the actual exceptional-slice ratio coordinate. -/
theorem literal_chart_slice_ratio
    {A L TA : Type} [CommRing A] [Field L] [Algebra ℂ A] [Algebra A L]
    [Algebra ℂ L] [IsScalarTower ℂ A L]
    {W X B : Over (Spec ↧ℂ)} (β : W ⟶ X) (b : X ⟶ B) (x : ComplexPoint B)
    (i : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶ W)
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X)
    (hn : (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))
      (ComplexPoint.specMap_comp_affineSpecStructureMap
        (IsScalarTower.toAlgHom ℂ A (integralClosure A L)))) ≫ j = i ≫ β)
    (ev : TA → integralClosure A L →ₐ[ℂ] ℂ)
    (H : TA → ComplexPoint (coveringSlice β b x))
    (hH : ∀ z, Point.map (pullback.fst β (pullback.fst b x)) (H z) =
      Point.map i ((ComplexPoint.affineSpecEquiv (integralClosure A L)).symm (ev z)))
    (v : ComplexPoint (exceptionalSlice b x) → OnePoint ℂ) (r : A)
    (hv : ∀ z y, Point.map j y = Point.map (pullback.fst b x) z →
      v z = ((ComplexPoint.affineSpecEquiv A y r : ℂ) : OnePoint ℂ)) :
    ∀ z, v (Point.map (sliceProjection β b x) (H z)) =
      ((ev z (algebraMap A (integralClosure A L) r) : ℂ) : OnePoint ℂ) := by
  let n : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap A) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))
      (ComplexPoint.specMap_comp_affineSpecStructureMap (IsScalarTower.toAlgHom ℂ A (integralClosure A L)))
  intro z
  let y := (ComplexPoint.affineSpecEquiv (integralClosure A L)).symm (ev z)
  have hbase : Point.map j (Point.map n y) =
      Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) (H z)) := by
    calc
      _ = Point.map (n ≫ j) y := (Point.map_comp_apply n j y).symm
      _ = Point.map (i ≫ β) y := congrArg (fun f => Point.map f y) hn
      _ = Point.map β (Point.map i y) := Point.map_comp_apply i β y
      _ = Point.map β (Point.map (pullback.fst β (pullback.fst b x)) (H z)) :=
        congrArg (Point.map β) (hH z).symm
      _ = _ := by
        rw [← Point.map_comp_apply, pullback.condition, Point.map_comp_apply]
  have hh := hv (Point.map (sliceProjection β b x) (H z)) (Point.map n y) hbase
  exact hh.trans (congrArg (fun a : ℂ => (a : OnePoint ℂ))
    (integral_coefficient_point_restriction_evaluation (ev z) r))

end AlgebraicGeometry.RamifiedNormalization.StageFour
