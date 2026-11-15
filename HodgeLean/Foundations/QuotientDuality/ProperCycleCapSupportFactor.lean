import HodgeLean.Foundations.QuotientDuality.ProperCycleCapNeighborhoodLift

/-! # Actual cap classes in the homology image of a neighborhood retract -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual open-neighborhood homotopy retraction places the ordinary cap class in the image of the original support homology.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, homotopy invariance and supported cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_factor_through_neighborhood_retract
    (X : TopCat.{0}) (S : Set X) (hS : IsClosed S)
    (U : Set X) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : TopCat.of S ⟶ TopCat.of U) (r : TopCat.of U ⟶ TopCat.of S)
    (hj : j ≫ (TopPair.ofSubset (X := X) U).map = (TopPair.ofSubset (X := X) S).map)
    (H : TopCat.Homotopy (𝟙 (TopCat.of U)) (r ≫ j)) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    ∃ b : Homology ℚ (TopCat.of S) q,
      homologyMap ℚ q (TopPair.ofSubset (X := X) S).map b =
        capCohomologyLinear ℚ X p q
          ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c := by
  obtain ⟨u, hu⟩ := properCycle_cap_lift_to_open_neighborhood X S hS U hU hSU p q a c
  have he : homologyMap ℚ q (r ≫ j) = homologyMap ℚ q (𝟙 (TopCat.of U)) :=
    (congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq q)).symm
  have hju : homologyMap ℚ q j (homologyMap ℚ q r u) = u := by
    simpa only [homologyMap_comp, LinearMap.comp_apply, homologyMap_id, LinearMap.id_apply]
      using LinearMap.congr_fun he u
  refine ⟨homologyMap ℚ q r u, ?_⟩
  calc
    _ = homologyMap ℚ q (TopPair.ofSubset (X := X) U).map
        (homologyMap ℚ q j (homologyMap ℚ q r u)) := by
      rw [← hj, homologyMap_comp]
      rfl
    _ = homologyMap ℚ q (TopPair.ofSubset (X := X) U).map u :=
      congrArg (homologyMap ℚ q (TopPair.ofSubset (X := X) U).map) hju
    _ = _ := hu

end HodgeLean.Foundations.QuotientDuality
