import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartPointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialRetractionPointMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphPointPair

/-! # The original ambient point map of actual collar chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual collar chart coordinates induce the original chart map on point homology, because their tangential interpolation retains the actual normal fibre.
Source: properCycle_tangential_retraction_point_map_eq; ProperCycleSupportCollar.chart_retraction_point_pair.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_retraction_point_map_eq
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (n : ℕ) :
    relativeHomologyMap ℚ n (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter) =
      relativeHomologyMap ℚ n
        (properCycle_chart_image_point_pair X E Y e W hWe z.val hzW y hcenter ≫
          properCycle_product_neighborhood_point_pair E Y y (e '' (W : Set X))
            ⟨z.val, hzW, hcenter⟩) := by
  unfold ProperCycleSupportCollar.chart_retraction_point_pair
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp,
    properCycle_tangential_retraction_point_map_eq]

/-- The actual collar chart point map is bijective on the original ambient local homology in every degree.
Source: properCycle_homeomorph_point_pair_bijective; properCycle_tangential_retraction_point_map_bijective.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_retraction_point_map_bijective
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0}) [T1Space Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter)) := by
  let H : W ≃ₜ e '' (W : Set X) := e.homeomorphOfImageSubsetSource hWe rfl
  have he : H (⟨z.val, hzW⟩ : W) =
      (⟨((0 : E), y), ⟨z.val, hzW, hcenter⟩⟩ : e '' (W : Set X)) := Subtype.ext hcenter
  have hH := properCycle_homeomorph_point_pair_bijective
    (TopCat.of W) (TopCat.of (e '' (W : Set X))) H ⟨z.val, hzW⟩ _ he n
  have ho : IsOpen (e '' (W : Set X)) := e.isOpen_image_of_subset_source W.isOpen hWe
  have hT := properCycle_tangential_retraction_point_map_bijective E Y y
    (e '' (W : Set X)) ho ⟨z.val, hzW, hcenter⟩
    (C.chart_tangential_coordinates e W hWe hWN hR)
    (C.chart_tangential_coordinates_on_normal_fibre e W hWe hWN hR y hflat) n
  unfold ProperCycleSupportCollar.chart_retraction_point_pair
  rw [relativeHomologyMap_comp]
  exact hT.comp hH

end HodgeLean.Foundations.QuotientDuality
