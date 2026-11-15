import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapLinear
import HodgeLean.Foundations.QuotientDuality.ProperCycleRetractedCapRestriction

/-! # The actual linear cap map on a neighborhood retract
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Excise the original relative ambient class to a support neighborhood, cap there, and apply the specified neighborhood retraction.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, supported cap and homotopy invariance.
HC no distance; AV milestone no distance. -/
def properCycle_collared_support_cap
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (r : TopCat.of U ⟶ TopCat.of S) (p q : ℕ) (c : Homology ℚ X (p + q)) :
    CohomologyWithSupport ℚ X S p →ₗ[ℚ] Homology ℚ (TopCat.of S) q :=
  (homologyMap ℚ q r).comp (properCycle_neighborhood_cap_linear X S U hS hU hSU p q c)

/-- The constructed linear support cap maps to the original absolute cap under the literal support inclusion.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, cap naturality and homotopy invariance.
HC no distance; AV milestone no distance. -/
lemma properCycle_collared_support_cap_inclusion
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : TopCat.of S ⟶ TopCat.of U) (r : TopCat.of U ⟶ TopCat.of S)
    (hj : j ≫ (TopPair.ofSubset (X := X) U).map = (TopPair.ofSubset (X := X) S).map)
    (H : TopCat.Homotopy (𝟙 (TopCat.of U)) (r ≫ j)) (p q : ℕ)
    (c : Homology ℚ X (p + q)) (a : CohomologyWithSupport ℚ X S p) :
    homologyMap ℚ q (TopPair.ofSubset (X := X) S).map
      (properCycle_collared_support_cap X S U hS hU hSU r p q c a) =
      capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c := by
  exact properCycle_retracted_neighborhood_cap_inclusion X S U hS hU hSU j hj r H p q a c

end HodgeLean.Foundations.QuotientDuality
