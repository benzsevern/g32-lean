import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartPointPair

/-! # Literal values of the actual collar point map in a flattened chart
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The constructed actual collar point map has precisely the original retraction's tangential chart coordinate and the original point's normal chart coordinate.
Source: ProperCycleSupportCollar.chart_tangential_coordinates_image; ProperCycleSupportCollar.chart_retraction_point_pair.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_retraction_point_pair_value
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (x : W) :
    (TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter)) x =
      ((e (C.retraction ⟨x.val, hWN x.property⟩).val).1, (e x.val).2) := by
  change (C.chart_tangential_coordinates e W hWe hWN hR
      ⟨e x.val, ⟨x.val, x.property, rfl⟩⟩, (e x.val).2) = _
  rw [C.chart_tangential_coordinates_image e W hWe hWN hR x.val x.property]

end HodgeLean.Foundations.QuotientDuality
