import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PointChartLifts
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffinePointSupport

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The two actual open chart inclusions cover the whole point fibre by their ratio coordinates. -/
theorem affine_slice_charts_cover
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (X : Over (Spec ↧ℂ))
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R))
    (j₁ : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
    (j₂ : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring v u)) ⟶ X)
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (hj₁ : ∀ a, Point.map p (Point.map j₁ a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a)
    (hj₂ : ∀ a, Point.map p (Point.map j₂ a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom v u) a)
    (hcover : ∀ x : X.left, (∃ a, j₁.left a = x) ∨ ∃ a, j₂.left a = x)
    (x : {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ}) :
    (∃ z, affineChartSliceMap u v φ hu hv X p j₁ hj₁ z = x) ∨
      ∃ z, affineChartSliceMap v u φ hv hu X p j₂ hj₂ z = x := by
  rcases hcover (x.val.left (IsLocalRing.closedPoint ℂ)) with hx | hx
  · left
    exact (mem_range_affineChartSliceMap u v φ hu hv X p j₁ hj₁ x).mpr hx
  · right
    exact (mem_range_affineChartSliceMap v u φ hv hu X p j₂ hj₂ x).mpr hx

/-- On the actual point fibre the first ratio chart misses precisely the second chart's zero parameter. -/
theorem affine_slice_chart_overlap
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (X : Over (Spec ↧ℂ))
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R))
    (j₁ : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
    (j₂ : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring v u)) ⟶ X)
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (hj₁ : ∀ a, Point.map p (Point.map j₁ a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a)
    (hj₂ : ∀ a, Point.map p (Point.map j₂ a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom v u) a)
    (hintersection : ∀ y : Spec ↧(RegularPairChart.ring v u),
      (∃ a, j₁.left a = j₂.left y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal)
    (z : ℂ) :
    affineChartSliceMap v u φ hv hu X p j₂ hj₂ z ∈
      Set.range (affineChartSliceMap u v φ hu hv X p j₁ hj₁) ↔ z ≠ 0 := by
  rw [mem_range_affineChartSliceMap]
  change (∃ a, j₁.left a = j₂.left
    (((affineChartPointFibreHomeomorph v u φ hv hu).symm z).val.left
      (IsLocalRing.closedPoint ℂ))) ↔ z ≠ 0
  rw [hintersection]
  exact not_congr (affine_chart_ratio_prime_iff_zero v u φ hv hu z)

end AlgebraicGeometry.RamifiedNormalization.StageFour
