import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineChartPointFibre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual coefficient square makes a scheme chart an inclusion over the complex base. -/
theorem chart_coefficient_square_over
    {R : Type} [CommRing R] [Algebra ℂ R] (u v : R)
    (M : Scheme) (π : M ⟶ Spec ↧R)
    (j : Spec ↧(RegularPairChart.ring u v) ⟶ M)
    (hj : j ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v))) :
    ∃ k : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶
        Over.mk (π ≫ ComplexPoint.affineSpecStructureMap R),
      k.left = j ∧
      ∀ a, Point.map (Over.homMk π rfl) (Point.map k a) =
        ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a := by
  let X := Over.mk (π ≫ ComplexPoint.affineSpecStructureMap R)
  let p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R) := Over.homMk π rfl
  let k : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X :=
    Over.homMk j (by
      change j ≫ (π ≫ ComplexPoint.affineSpecStructureMap R) =
        ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)
      rw [← Category.assoc, hj]
      exact ComplexPoint.specMap_comp_affineSpecStructureMap (regularPairCoefficientAlgHom u v))
  have hk : k ≫ p = Over.homMk
      (Spec.map (CommRingCat.ofHom (regularPairCoefficientAlgHom u v).toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap (regularPairCoefficientAlgHom u v)) := by
    apply Over.OverMorphism.ext
    exact hj
  refine ⟨k, rfl, ?_⟩
  intro a
  change Point.map p (Point.map k a) = _
  rw [← Point.map_comp_apply, hk]
  rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
