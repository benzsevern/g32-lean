import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedChartPointVanishing
import HodgeLean.Foundations.QuotientDuality.ProperCycleHomologyImagePointValues

/-! # Actual component image propagation across connected chart regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- A single nonzero point value of an actual homology image forces its actual continuous-map range to contain every point of a connected original chart region.
Source: properCycle_connected_chart_point_vanishing; properCycle_local_orientation_image_outside_range.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_chart_image_range
    (X Y Z : TopCat.{0}) [T2Space X] [PreconnectedSpace Y]
    (d : ℕ) (e : OpenPartialHomeomorph X (Fin d → ℂ))
    (j : Y ⟶ X) (hj : ∀ y, j y ∈ e.source)
    (f : Z ⟶ X) (c : Homology ℚ Z (2*d)) (p : Y)
    (hp : localOrientation X (2*d) (homologyMap ℚ (2*d) f c) (j p) ≠ 0) :
    ∀ y : Y, j y ∈ Set.range f := by
  intro y
  by_contra hy
  have hz := properCycle_local_orientation_image_outside_range f (j y) hy (2*d) c
  exact hp ((properCycle_connected_chart_point_vanishing X Y d e j hj
    (homologyMap ℚ (2*d) f c) p y).mpr hz)

end HodgeLean.Foundations.QuotientDuality
