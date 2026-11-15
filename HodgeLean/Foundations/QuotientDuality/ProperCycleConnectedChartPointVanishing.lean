import HodgeLean.Foundations.QuotientDuality.ProperCycleChartZeroLocallyConstant

/-! # Actual point vanishing along connected original chart regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Original top homology point vanishing agrees at every two points of a connected region lying in the original chart source.
Source: properCycle_chart_zero_locally_constant; IsLocallyConstant.apply_eq_of_preconnectedSpace.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_chart_point_vanishing
    (X Y : TopCat.{0}) [T2Space X] [PreconnectedSpace Y]
    (d : ℕ) (e : OpenPartialHomeomorph X (Fin d → ℂ))
    (j : Y ⟶ X) (hj : ∀ y, j y ∈ e.source)
    (c : Homology ℚ X (2*d)) (p q : Y) :
    localOrientation X (2*d) c (j p) = 0 ↔ localOrientation X (2*d) c (j q) = 0 := by
  let f : C(Y, e.source) := ⟨fun y => ⟨j y, hj y⟩, j.hom.continuous.subtype_mk _⟩
  have h := (properCycle_chart_zero_locally_constant X d e c).comp_continuous f.continuous
  exact Iff.of_eq (h.apply_eq_of_preconnectedSpace p q)

end HodgeLean.Foundations.QuotientDuality
