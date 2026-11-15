import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriadProjection

/-! # The literal relative quotient through the original triad-to-union map
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative-to-triad projection followed by the original triad-to-union map is the literal nested-support quotient map.
Source: properCycle_relative_to_triad_projection; triadRelativeChainProjection_triadToUnionRelativeChainMap; relativeChainProjection_naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triad_union
    (X : TopCat.{0}) (A B : Set X) :
    properCycle_relative_to_triad_chain_map X A B ≫ triadToUnionRelativeChainMap ℚ X A B =
      (relativeChainFunctor ℚ).map
        (TopPair.ofSubsetHom (𝟙 X) (fun _ hz => (Set.subset_union_left : A ⊆ A ∪ B) hz)) := by
  let f := TopPair.ofSubsetHom (𝟙 X) (fun _ hz => (Set.subset_union_left : A ⊆ A ∪ B) hz)
  letI : Epi (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)) := by
    unfold relativeChainProjection
    infer_instance
  apply (cancel_epi (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A))).mp
  rw [← Category.assoc, properCycle_relative_to_triad_projection,
    triadRelativeChainProjection_triadToUnionRelativeChainMap]
  have h := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f
  change _ = (((AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫ _ at h
  have hi := ((AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map_id X
  exact (h.trans ((congrArg (fun m => m ≫
    relativeChainProjection ℚ (TopPair.ofSubset (X := X) (A ∪ B))) hi).trans
      (Category.id_comp _))).symm

end HodgeLean.Foundations.QuotientDuality
