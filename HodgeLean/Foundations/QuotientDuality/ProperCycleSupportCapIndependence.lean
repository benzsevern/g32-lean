import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRetractionComparison

/-! # Independence of the actual support cap from retained neighborhood choices
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Any retained collar gives the same actual support cap as a support-fixing collar, by comparing original cap values on a common open neighborhood.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, homotopy invariance and cap excision.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.cap_eq_of_fixed
    {X : TopCat.{0}} {S : Set X} (C D : ProperCycleSupportCollar X S)
    (hfixed : ∀ (t : unitInterval) (s : TopCat.of S),
      C.deformation (t, C.inclusion s) = C.inclusion s)
    (hS : IsClosed S) (p q : ℕ) (c : Homology ℚ X (p + q)) :
    D.cap hS p q c = C.cap hS p q c := by
  obtain ⟨V, hV, hSV, hVC, hVD, ⟨H⟩⟩ := properCycle_support_collar_common_retractions C D hfixed
  let f := TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVC S)
  let g := TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVD S)
  have he : homologyMap ℚ q (g ≫ D.retraction) = homologyMap ℚ q (f ≫ C.retraction) :=
    congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq q)
  apply LinearMap.ext
  intro a
  let u := properCycle_neighborhood_cap X S V hS hV hSV p q a c
  have hC := properCycle_neighborhood_cap_restriction X S C.neighborhood V
    hS C.isOpen hV C.contains hSV hVC p q a c
  have hD := properCycle_neighborhood_cap_restriction X S D.neighborhood V
    hS D.isOpen hV D.contains hSV hVD p q a c
  change homologyMap ℚ q D.retraction
    (properCycle_neighborhood_cap X S D.neighborhood hS D.isOpen D.contains p q a c) =
    homologyMap ℚ q C.retraction
      (properCycle_neighborhood_cap X S C.neighborhood hS C.isOpen C.contains p q a c)
  rw [← hD, ← hC]
  calc
    _ = homologyMap ℚ q (g ≫ D.retraction) u :=
      (LinearMap.congr_fun (homologyMap_comp ℚ q g D.retraction) u).symm
    _ = homologyMap ℚ q (f ≫ C.retraction) u := LinearMap.congr_fun he u
    _ = _ := LinearMap.congr_fun (homologyMap_comp ℚ q f C.retraction) u

end HodgeLean.Foundations.QuotientDuality
