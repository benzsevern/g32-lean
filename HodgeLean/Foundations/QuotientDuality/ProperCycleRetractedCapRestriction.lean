import HodgeLean.Foundations.QuotientDuality.ProperCycleRetractionHomology

/-! # Actual support cap values under nested neighborhood retractions -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The support homology value of the actual excised cap is unchanged on nested neighborhoods with compatible original support inclusions and actual retractions.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, homotopy invariance and supported cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_retracted_cap_restriction
    (X : TopCat.{0}) (S U V : Set X) (hS : IsClosed S) (hU : IsOpen U) (hV : IsOpen V)
    (hSU : S ⊆ U) (hSV : S ⊆ V) (hVU : V ⊆ U)
    (jU : TopCat.of S ⟶ TopCat.of U) (jV : TopCat.of S ⟶ TopCat.of V)
    (hj : jV ≫ TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVU S) = jU)
    (rU : TopCat.of U ⟶ TopCat.of S) (rV : TopCat.of V ⟶ TopCat.of S)
    (hjr : jU ≫ rU = 𝟙 (TopCat.of S))
    (H : TopCat.Homotopy (𝟙 (TopCat.of V)) (rV ≫ jV)) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    properCycle_retracted_neighborhood_cap X S V hS hV hSV rV p q a c =
      properCycle_retracted_neighborhood_cap X S U hS hU hSU rU p q a c := by
  let i := TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVU S)
  have ht : jV ≫ (i ≫ rU) = 𝟙 (TopCat.of S) := by rw [← Category.assoc, hj, hjr]
  have he := properCycle_homology_retractions_eq jV rV (i ≫ rU) ht H q
  have hc := properCycle_neighborhood_cap_restriction X S U V hS hU hV hSU hSV hVU p q a c
  change homologyMap ℚ q rV _ = homologyMap ℚ q rU _
  exact (LinearMap.congr_fun he _).trans
    ((LinearMap.congr_fun (homologyMap_comp ℚ q i rU) _).trans
      (congrArg (homologyMap ℚ q rU) hc))

end HodgeLean.Foundations.QuotientDuality
