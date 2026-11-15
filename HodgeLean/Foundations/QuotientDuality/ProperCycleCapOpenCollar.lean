import HodgeLean.Foundations.QuotientDuality.ProperCycleCapSupportFactor

/-! # Original support homology from actual open collar maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual open collar and its homotopy retraction place each cap class in the image of the original support inclusion.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; Rourke and Sanderson, Introduction to Piecewise-Linear Topology, chapter 3.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_factor_through_open_collar
    (X : TopCat.{0}) (S : Set X) (hS : IsClosed S)
    (U : TopCat.{0}) (j : TopCat.of S ⟶ U) (k : U ⟶ X)
    (hj : j ≫ k = (TopPair.ofSubset (X := X) S).map)
    (hk : Topology.IsOpenEmbedding k) (r : U ⟶ TopCat.of S)
    (H : TopCat.Homotopy (𝟙 U) (r ≫ j)) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    ∃ b : Homology ℚ (TopCat.of S) q,
      homologyMap ℚ q (TopPair.ofSubset (X := X) S).map b =
        capCohomologyLinear ℚ X p q
          ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c := by
  let V := Set.range k
  have hSV : S ⊆ V := by
    intro s hs
    exact ⟨j ⟨s, hs⟩, ConcreteCategory.congr_hom hj ⟨s, hs⟩⟩
  obtain ⟨v, hv⟩ := properCycle_cap_lift_to_open_neighborhood X S hS V hk.isOpen_range hSV p q a c
  let e : U ≃ₜ V := hk.isEmbedding.toHomeomorph
  let ei : TopCat.of V ⟶ U := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hei : ei ≫ k = (TopPair.ofSubset (X := X) V).map := by
    ext z : 1
    exact congrArg Subtype.val (e.apply_symm_apply z)
  let u := homologyMap ℚ q ei v
  have hu : homologyMap ℚ q k u =
      capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c := by
    change homologyMap ℚ q k (homologyMap ℚ q ei v) = _
    rw [← LinearMap.comp_apply, ← homologyMap_comp, hei]
    exact hv
  have he : homologyMap ℚ q (r ≫ j) = homologyMap ℚ q (𝟙 U) :=
    (congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq q)).symm
  have hju : homologyMap ℚ q j (homologyMap ℚ q r u) = u := by
    simpa only [homologyMap_comp, LinearMap.comp_apply, homologyMap_id, LinearMap.id_apply]
      using LinearMap.congr_fun he u
  refine ⟨homologyMap ℚ q r u, ?_⟩
  change homologyMap ℚ q (TopPair.ofSubset (X := X) S).map
    (homologyMap ℚ q r u) = _
  calc
    _ = homologyMap ℚ q k (homologyMap ℚ q j (homologyMap ℚ q r u)) := by
      have hm : homologyMap ℚ q (TopPair.ofSubset (X := X) S).map =
          (homologyMap ℚ q k).comp (homologyMap ℚ q j) := by
        rw [← hj, homologyMap_comp]
      exact LinearMap.congr_fun hm _
    _ = homologyMap ℚ q k u := congrArg (homologyMap ℚ q k) hju
    _ = _ := hu

end HodgeLean.Foundations.QuotientDuality
