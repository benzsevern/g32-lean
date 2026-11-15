import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCollar
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Actual retraction fibres and original support point pairs
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The retained collar retraction sends the complement of its literal fibre to the complement of the specified support point.
Source: ProperCycleSupportCollar.retraction; TopPair.ofSubsetHom.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.pointPairMap {X : TopCat.{0}} {S : Set X}
    (C : ProperCycleSupportCollar X S) (z : S) :
    TopPair.ofSubset (X := TopCat.of C.neighborhood) (C.retraction ⁻¹' ({z} : Set S)ᶜ) ⟶
      pointComplementPair z :=
  TopPair.ofSubsetHom C.retraction (fun _ h => h)

/-- The original point value of the constructed support cap is its original neighborhood cap projected modulo the literal retraction fibre and mapped by the actual point-pair map.
Source: properCycle_relative_homology_projection_naturality; ProperCycleSupportCollar.cap.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.cap_point_projection {X : TopCat.{0}} {S : Set X}
    (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (z : S) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p+q)) :
    localOrientation (TopCat.of S) q (C.cap hS p q c a) z =
      relativeHomologyMap ℚ q (C.pointPairMap z)
        ((relativeHomologyProjection ℚ
          (TopPair.ofSubset (X := TopCat.of C.neighborhood)
            (C.retraction ⁻¹' ({z} : Set S)ᶜ)) q).hom
          (properCycle_neighborhood_cap X S C.neighborhood hS C.isOpen C.contains p q a c)) := by
  exact (properCycle_relative_homology_projection_naturality (C.pointPairMap z) q
    (properCycle_neighborhood_cap X S C.neighborhood hS C.isOpen C.contains p q a c)).symm

end HodgeLean.Foundations.QuotientDuality
