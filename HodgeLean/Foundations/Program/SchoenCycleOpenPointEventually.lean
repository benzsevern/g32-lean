import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- An eventual identity on the actual open scheme gives the same eventual identity near its original ambient complex point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_open_point_eventually
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (x : ComplexPoint (ComplexPoint.openScheme X U))
    (P : ComplexPoint X → Prop)
    (h : ∀ᶠ q in 𝓝 x, P (Point.map (ComplexPoint.openInclusion X U) q)) :
    ∀ᶠ q in 𝓝 (Point.map (ComplexPoint.openInclusion X U) x), P q := by
  rw [← (ComplexPoint.isOpenEmbedding_map_open X U).map_nhds_eq x]
  exact h

#print axioms s2e_open_point_eventually
end HodgeLean.Foundations.Program
