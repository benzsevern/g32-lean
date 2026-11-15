import HodgeLean.Foundations.QuotientDuality.LocalChartCalibration

/-! Dense pointwise normalization calibrates the explicit local chart class. -/
noncomputable section
set_option maxHeartbeats 400000
open Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem chart_orientation_normalized_of_dense
    (X : TopCat.{0}) [T2Space X] (d : ℕ) (o : LocalRationalOrientation X (2 * d))
    (S : Set X) (hS : Dense S)
    (E : OpenPartialHomeomorph X (Fin d → ℂ)) (x : X) (hx : x ∈ E.source)
    (hn : ∀ y ∈ S, ∀ hy : y ∈ chartOrientationNeighborhood d E x hx,
      o.generator y = localClassOfChart d E y
        (chartOrientationNeighborhood_subset_source d E x hx hy)) :
    o.generator x = localClassOfChart d E x hx := by
  obtain ⟨y, hyU, hyS⟩ := hS.inter_open_nonempty
    (chartOrientationNeighborhood d E x hx) (chartOrientationNeighborhood d E x hx).isOpen
    ⟨x, mem_chartOrientationNeighborhood d E x hx⟩
  exact chart_orientation_normalized_of_one_point X d o E x hx y hyU (hn y hyS hyU)

#print axioms chart_orientation_normalized_of_dense
end HodgeLean.Foundations.QuotientDuality
