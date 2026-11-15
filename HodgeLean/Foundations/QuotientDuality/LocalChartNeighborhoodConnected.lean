import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartNeighborhoodOrientation

/-! Connectedness of the explicit chart orientation neighborhood. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem chart_orientation_neighborhood_preconnected {M : Type} [TopologicalSpace M]
    (d : ℕ) (E : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ E.source) :
    PreconnectedSpace (chartOrientationNeighborhood d E x hx) := by
  have hb : _root_.IsPreconnected (standardOrientationBall (d * 2) : Set (Fin (d * 2) → ℝ)) :=
    (convex_ball (0 : Fin (d * 2) → ℝ) (standardOrientationRadius (d * 2))).isPreconnected
  have hc : _root_.IsPreconnected (standardComplexOrientationNeighborhood d : Set (Fin d → ℂ)) :=
    hb.image (standardRealToComplexMap d) (complexRealHomeomorph d).symm.continuous.continuousOn
  have hU : _root_.IsPreconnected (chartOrientationNeighborhood d E x hx : Set M) :=
    hc.image (chartOrientationEmbeddingMap d E x hx)
      (chartOrientationEmbeddingMap d E x hx).hom.continuous.continuousOn
  exact isPreconnected_iff_preconnectedSpace.mp hU

#print axioms chart_orientation_neighborhood_preconnected
end HodgeLean.Foundations.QuotientDuality
