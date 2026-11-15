import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartObjects

noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra

/-- Flat chart base change retaining the actual natural conormal morphism. -/
def pairedC3CanonicalChartConormalIso {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    (Scheme.Modules.pullback (pairedC3ChartInclusion k i)).obj
      (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)) ≅
        Conormal.sheaf (Spec.map (pairedC3ChartProjection e i)) := by
  letI := paired_c3_polynomial_coordinate_inclusion_immersion (A := ℂ) e
  letI : IsClosedImmersion (Spec.map (pairedC3ChartProjection e i)) :=
    IsClosedImmersion.spec_of_surjective _ (paired_c3_coordinate_chart_map_surjective e i)
  exact Conormal.flatBaseChangeIso (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)
    (Spec.map (pairedC3ChartProjection e i)) (pairedC3ChartInclusion n (e i))
    (pairedC3ChartInclusion k i) (paired_c3_normalized_coordinate_chart_isPullback e i).flip

/-- The chart isomorphism has the original natural conormal comparison as its forward morphism. -/
theorem paired_c3_canonical_chart_iso_hom {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    (pairedC3CanonicalChartConormalIso e i).hom =
      Conormal.comparisonMap (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)
        (Spec.map (pairedC3ChartProjection e i)) (pairedC3ChartInclusion n (e i))
        (pairedC3ChartInclusion k i) (paired_c3_chart_diagram_commutes e i) := by
  rfl

#print axioms pairedC3CanonicalChartConormalIso
end HodgeLean.Foundations.Program.G32Native
