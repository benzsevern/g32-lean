import HodgeLean.Foundations.QuotientDuality.ProperCycleNestedSupportRetractions
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapEnlargement

/-! # Actual support cap naturality for nested original supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original inclusion of supports intertwines their actual cap maps and the original enlargement map, using only a retained support-fixing source deformation.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of cap products with support.
HC no distance; AV milestone no distance. -/
lemma properCycle_collared_support_cap_enlargement
    {X : TopCat.{0}} {S T : Set X} (hST : S ⊆ T)
    (C : ProperCycleSupportCollar X S) (D : ProperCycleSupportCollar X T)
    (hfixed : ∀ (t : unitInterval) (s : TopCat.of S),
      C.deformation (t, C.inclusion s) = C.inclusion s)
    (hS : IsClosed S) (hT : IsClosed T) (p q : ℕ)
    (c : Homology ℚ X (p+q)) (a : CohomologyWithSupport ℚ X S p) :
    homologyMap ℚ q (TopCat.ofHom (ContinuousMap.inclusion hST)) (C.cap hS p q c a) =
      D.cap hT p q c (enlargeSupport ℚ X hST p a) := by
  obtain ⟨V, hV, hSV, hVC, hVD, ⟨H⟩⟩ :=
    properCycle_nested_support_common_retractions hST C D hfixed
  let f := TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVC S)
  let g := TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVD T)
  let st : TopCat.of S ⟶ TopCat.of T := TopCat.ofHom (ContinuousMap.inclusion hST)
  have he : homologyMap ℚ q (g ≫ D.retraction) = homologyMap ℚ q (f ≫ C.retraction ≫ st) :=
    congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq q)
  let u := properCycle_neighborhood_cap X S V hS hV hSV p q a c
  have hC := properCycle_neighborhood_cap_restriction X S C.neighborhood V
    hS C.isOpen hV C.contains hSV hVC p q a c
  have hD := properCycle_neighborhood_cap_restriction X S D.neighborhood V
    hS D.isOpen hV (hST.trans D.contains) hSV hVD p q a c
  have hE := properCycle_neighborhood_cap_enlarge_support X S T D.neighborhood
    hS hT D.isOpen hST D.contains p q a c
  change homologyMap ℚ q st (homologyMap ℚ q C.retraction
    (properCycle_neighborhood_cap X S C.neighborhood hS C.isOpen C.contains p q a c)) =
    homologyMap ℚ q D.retraction (properCycle_neighborhood_cap X T D.neighborhood hT
      D.isOpen D.contains p q (enlargeSupport ℚ X hST p a) c)
  rw [← hC, ← hE, ← hD]
  calc
    _ = homologyMap ℚ q (f ≫ C.retraction ≫ st) u := by
      simp only [homologyMap_comp, LinearMap.comp_apply]
      rfl
    _ = homologyMap ℚ q (g ≫ D.retraction) u := LinearMap.congr_fun he.symm u
    _ = _ := by
      simp only [homologyMap_comp, LinearMap.comp_apply]
      rfl

end HodgeLean.Foundations.QuotientDuality
