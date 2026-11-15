import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalOrientationDegree

/-! # Literal degree transport of actual ambient orientation lines
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Literal transport of the ambient homology degree retains bijectivity of its specified original point orientation line.
Source: orientationLine; equality transport.
HC no distance; AV milestone no distance. -/
lemma properCycle_orientation_line_degree_bijective
    (X : TopCat.{0}) (n m : ℕ) (h : n = m) (c : Homology ℚ X n) (x : X)
    (hc : Function.Bijective (orientationLine X n c x)) :
    Function.Bijective (orientationLine X m
      ((eqToIso (congrArg (fun j => Homology ℚ X j) h)).hom.hom c) x) := by
  subst m
  exact hc

end HodgeLean.Foundations.QuotientDuality
