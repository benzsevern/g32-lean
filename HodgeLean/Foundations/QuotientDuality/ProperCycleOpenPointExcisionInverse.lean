import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport

/-! # The original inverse point excision with its literal pair identification
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Inverse open point excision is the original neighborhood inverse followed by the identity identification of its point-complement pair.
Source: properCycle_open_local_homology_iso; neighborhoodPointComplementRelativeHomologyIso.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_local_homology_inverse_map
    (X : TopCat.{0}) [T1Space X] (W : Opens X) (w : W) (n : ℕ)
    (c : orientationGroup X n w.val) :
    let e : neighborhoodPointComplementPair (W : Set X) w.val ≅ pointComplementPair w :=
      TopPair.isoOfSubset (Homeomorph.refl W) (by
        intro u
        change u ≠ w ↔ u.val ≠ w.val
        exact not_congr Subtype.ext_iff)
    (properCycle_open_local_homology_iso X W w n).inv.hom c =
      relativeHomologyMap ℚ n e.hom
        ((neighborhoodPointComplementRelativeHomologyIso (W : Set X) w.val W.isOpen w.property n).inv.hom c) := by
  dsimp only
  change relativeHomologyMap ℚ n _ _ = relativeHomologyMap ℚ n _ _
  congr 1

end HodgeLean.Foundations.QuotientDuality
