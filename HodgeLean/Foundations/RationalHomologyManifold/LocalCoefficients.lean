import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.QuotientDuality.LocalOrientationSheaf

/-! Propagation of equality of local values on a connected orientation section.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equality of two local values at one point propagates over a preconnected space.
Source: Bredon, Sheaf Theory, second edition, V.9, the orientation sheaf and constant local coefficients.
HC no distance; AV milestone no distance.
-/
theorem localization_eq_of_eq_at_point (X : TopCat.{0}) [T2Space X]
    [PreconnectedSpace X] (n : ℕ) (o : LocalRationalOrientation X n)
    (c d : Homology ℚ X n) (x : X)
    (hx : localization X n c x = localization X n d x) :
    localization X n c = localization X n d := by
  obtain ⟨r, hr⟩ := local_values_constant X n o c
  obtain ⟨s, hs⟩ := local_values_constant X n o d
  have hrs : r = s := (o.generates x).1 (by
    change r • o.generator x = s • o.generator x
    exact (hr x).symm.trans (hx.trans (hs x)))
  funext y
  exact (hr y).trans (by rw [hrs]; exact (hs y).symm)

#print axioms localization_eq_of_eq_at_point
end HodgeLean.Foundations.RationalHomologyManifold
