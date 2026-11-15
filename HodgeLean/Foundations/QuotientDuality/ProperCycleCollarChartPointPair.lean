import HodgeLean.Foundations.QuotientDuality.ProperCycleChartImagePointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartNormalFibre

/-! # Actual collar point maps in original flattened chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The original chart-image point map followed by the actual tangential collar coordinates, with the normal coordinate retained literally.
Source: properCycle_chart_image_point_pair; ProperCycleSupportCollar.chart_tangential_coordinates_on_normal_fibre.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.chart_retraction_point_pair
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) :
    pointComplementPair (⟨z.val, hzW⟩ : W) ⟶ pointComplementPair ((0 : E), y) :=
  properCycle_chart_image_point_pair X E Y e W hWe z.val hzW y hcenter ≫
    properCycle_tangential_retraction_point_pair E Y y (e '' (W : Set X))
      ⟨z.val, hzW, hcenter⟩ (C.chart_tangential_coordinates e W hWe hWN hR)
      (C.chart_tangential_coordinates_on_normal_fibre e W hWe hWN hR y hflat)

end HodgeLean.Foundations.QuotientDuality
