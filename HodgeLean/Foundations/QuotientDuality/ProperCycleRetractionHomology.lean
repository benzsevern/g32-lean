import HodgeLean.Foundations.QuotientDuality.ProperCycleRetractedNeighborhoodCap

/-! # Actual homology maps of neighborhood retractions -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual retractions of a homotopy retract induce the same original homology map.
Source: Hatcher, Algebraic Topology, section 2.1, homotopy invariance and retractions.
HC no distance; AV milestone no distance. -/
lemma properCycle_homology_retractions_eq
    {S U : TopCat.{0}} (j : S ⟶ U) (r t : U ⟶ S) (hjt : j ≫ t = 𝟙 S)
    (H : TopCat.Homotopy (𝟙 U) (r ≫ j)) (q : ℕ) :
    homologyMap ℚ q r = homologyMap ℚ q t := by
  have he : homologyMap ℚ q (r ≫ j) = homologyMap ℚ q (𝟙 U) :=
    (congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq q)).symm
  ext u
  have hju : homologyMap ℚ q j (homologyMap ℚ q r u) = u := by
    simpa only [homologyMap_comp, LinearMap.comp_apply, homologyMap_id, LinearMap.id_apply]
      using LinearMap.congr_fun he u
  calc
    _ = homologyMap ℚ q (j ≫ t) (homologyMap ℚ q r u) := by
      rw [hjt, homologyMap_id, LinearMap.id_apply]
    _ = homologyMap ℚ q t (homologyMap ℚ q j (homologyMap ℚ q r u)) := by
      rw [homologyMap_comp, LinearMap.comp_apply]
    _ = _ := congrArg (homologyMap ℚ q t) hju

end HodgeLean.Foundations.QuotientDuality
