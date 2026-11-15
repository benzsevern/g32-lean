import HodgeLean.Foundations.QuotientDuality.LocalSupportedCoefficients
import HodgeLean.Foundations.QuotientDuality.LocalChartNeighborhoodConnected

/-! One correctly normalized point calibrates the entire explicit chart orientation neighborhood. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem chart_orientation_normalized_of_one_point
    (X : TopCat.{0}) [T2Space X] (d : ℕ) (o : LocalRationalOrientation X (2 * d))
    (E : OpenPartialHomeomorph X (Fin d → ℂ)) (x : X) (hx : x ∈ E.source)
    (y : X) (hy : y ∈ chartOrientationNeighborhood d E x hx)
    (hn : o.generator y = localClassOfChart d E y
      (chartOrientationNeighborhood_subset_source d E x hx hy)) :
    o.generator x = localClassOfChart d E x hx := by
  let U := chartOrientationNeighborhood d E x hx
  letI : PreconnectedSpace U := chart_orientation_neighborhood_preconnected d E x hx
  obtain ⟨f, hflc, hf⟩ := relative_open_coefficients X (2 * d) o U
    (chartOrientationNeighborhoodClass d E x hx)
  have hfc (z : U) : localClassOfChart d E z.val
      (chartOrientationNeighborhood_subset_source d E x hx z.property) =
      f z • o.generator z.val :=
    (chartOrientationNeighborhoodClass_restrict d E x hx z.val z.property).symm.trans (hf z)
  let yU : U := ⟨y, hy⟩
  let xU : U := ⟨x, mem_chartOrientationNeighborhood d E x hx⟩
  have hy1 : f yU = 1 := (o.generates y).1 (by
    change f yU • o.generator y = (1 : ℚ) • o.generator y
    exact (hfc yU).symm.trans (hn.symm.trans (one_smul ℚ _).symm))
  have hx1 : f xU = 1 := (hflc.apply_eq_of_preconnectedSpace xU yU).trans hy1
  have he := hfc xU
  rw [hx1, one_smul] at he
  exact he.symm

#print axioms chart_orientation_normalized_of_one_point
end HodgeLean.Foundations.QuotientDuality
