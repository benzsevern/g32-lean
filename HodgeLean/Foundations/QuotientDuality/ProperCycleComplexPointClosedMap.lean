import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMarkedTriangulation

/-! # Original complex points as actual algebraic closed marks -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

/-- An original complex point is an actual closed immersion over its original complex base.
Source: AlgebraicGeometry.isClosedImmersion_of_comp_eq_id.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_point_closed_immersion
    (X : Over (Spec ↧ℂ)) (x : ComplexPoint X) : IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)

/-- The original complex-point closed map has exactly its specified singleton as its analytic image.
Source: Point.map; Over.w; Category.id_comp.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_point_map_range
    (X : Over (Spec ↧ℂ)) (x : ComplexPoint X) : Set.range (Point.map x) = {x} := by
  have he (z : ComplexPoint (Over.mk (𝟙 (Spec ↧ℂ)))) : Point.map x z = x := by
    apply Over.OverMorphism.ext
    have hz : z.left = 𝟙 _ := by simpa using Over.w z
    change z.left ≫ x.left = x.left
    rw [hz, Category.id_comp]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact he z
  · intro hy
    have hy' : y = x := hy
    subst y
    exact ⟨𝟙 (Over.mk (𝟙 (Spec ↧ℂ))), he _⟩

end HodgeLean.Foundations.QuotientDuality
