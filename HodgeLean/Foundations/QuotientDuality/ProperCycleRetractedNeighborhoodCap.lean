import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapRestriction
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! # Actual support homology values from the excised neighborhood cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Apply an actual neighborhood retraction to the cap class constructed using the excised original relative fundamental class.
Source: Hatcher, Algebraic Topology, section 3.3, cap products with support.
HC no distance; AV milestone no distance. -/
noncomputable def properCycle_retracted_neighborhood_cap
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (r : TopCat.of U ⟶ TopCat.of S) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) : Homology ℚ (TopCat.of S) q :=
  homologyMap ℚ q r (properCycle_neighborhood_cap X S U hS hU hSU p q a c)

/-- Retraction of the excised original cap class has the required original ordinary inclusion image whenever the actual neighborhood homotopy retracts onto the original support.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, homotopy invariance and cap products with support.
HC no distance; AV milestone no distance. -/
lemma properCycle_retracted_neighborhood_cap_inclusion
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : TopCat.of S ⟶ TopCat.of U)
    (hj : j ≫ (TopPair.ofSubset (X := X) U).map = (TopPair.ofSubset (X := X) S).map)
    (r : TopCat.of U ⟶ TopCat.of S) (H : TopCat.Homotopy (𝟙 (TopCat.of U)) (r ≫ j))
    (p q : ℕ) (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    homologyMap ℚ q (TopPair.ofSubset (X := X) S).map
      (properCycle_retracted_neighborhood_cap X S U hS hU hSU r p q a c) =
      capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c := by
  let u := properCycle_neighborhood_cap X S U hS hU hSU p q a c
  have he : homologyMap ℚ q (r ≫ j) = homologyMap ℚ q (𝟙 (TopCat.of U)) :=
    (congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq q)).symm
  have hju : homologyMap ℚ q j (homologyMap ℚ q r u) = u := by
    simpa only [homologyMap_comp, LinearMap.comp_apply, homologyMap_id, LinearMap.id_apply]
      using LinearMap.congr_fun he u
  have hm : homologyMap ℚ q (TopPair.ofSubset (X := X) S).map =
      (homologyMap ℚ q (TopPair.ofSubset (X := X) U).map).comp (homologyMap ℚ q j) := by
    rw [← hj, homologyMap_comp]
  exact (LinearMap.congr_fun hm (homologyMap ℚ q r u)).trans
    ((congrArg (homologyMap ℚ q (TopPair.ofSubset (X := X) U).map) hju).trans
      (properCycle_neighborhood_cap_inclusion X S U hS hU hSU p q a c))

end HodgeLean.Foundations.QuotientDuality
