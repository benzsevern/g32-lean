import HodgeLean.Foundations.QuotientDuality.OrientationDefs

/-! # Literal degree transport of specified ambient point orientations
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original local orientation commutes with literal transport of the ambient homology degree.
Source: localOrientation; equality transport.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_orientation_degree
    (X : TopCat.{0}) (n m : ℕ) (h : n = m) (c : Homology ℚ X n) (x : X) :
    localOrientation X m ((eqToIso (congrArg (fun j => Homology ℚ X j) h)).hom.hom c) x =
      (eqToIso (congrArg (fun j => orientationGroup X j x) h)).hom.hom
        (localOrientation X n c x) := by
  subst m
  rfl

end HodgeLean.Foundations.QuotientDuality
