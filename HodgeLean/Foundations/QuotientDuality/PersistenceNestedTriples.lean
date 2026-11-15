import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseTriple
import HodgeLean.Foundations.QuotientDuality.PersistenceNestedSubsetPairs

/-! Actual relative-triple sequence maps for nested locus neighbourhoods. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual relative-triple map from the smaller neighbourhood to the larger one. -/
def persistenceNestedSubsetTripleMap
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) :
    persistenceSubsetTripleChainSequence K A M hAM ⟶
      persistenceSubsetTripleChainSequence K A N (hAM.trans hMN) := by
  let f := persistenceSubsetNeighbourhoodInclusion A M hAM
  let g : TopCat.of M ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let f' := persistenceSubsetNeighbourhoodInclusion A N (hAM.trans hMN)
  let g' : TopCat.of N ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let b := persistenceSubsetNeighbourhoodInclusion M N hMN
  have h₁ : f ≫ b = (𝟙 (TopCat.of A)) ≫ f' := by
    apply TopCat.ext
    intro a
    rfl
  have h₂ : g ≫ (𝟙 (TopCat.of X)) = b ≫ g' := by
    apply TopCat.ext
    intro m
    rfl
  exact persistenceRelativeTripleChainSequenceMap K f g f' g'
    (Topology.IsEmbedding.inclusion hAM) Topology.IsEmbedding.subtypeVal
    (Topology.IsEmbedding.inclusion (hAM.trans hMN)) Topology.IsEmbedding.subtypeVal
    (𝟙 (TopCat.of A)) b (𝟙 (TopCat.of X)) h₁ h₂

lemma persistence_nested_subset_triple_left_map
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) :
    (persistenceNestedSubsetTripleMap K A M N hAM hMN).τ₁ =
      (relativeChainFunctor K).map (persistenceNestedSubsetPairMap A M N hAM hMN) := by
  dsimp only [persistenceNestedSubsetTripleMap, persistenceRelativeTripleChainSequenceMap]
  apply congrArg ((relativeChainFunctor K).map)
  apply persistence_pair_hom_ext
  rfl

lemma persistence_nested_subset_triple_middle_map
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) :
    (persistenceNestedSubsetTripleMap K A M N hAM hMN).τ₂ =
      𝟙 ((relativeChainFunctor K).obj (TopPair.ofSubset (X := TopCat.of X) A)) := by
  dsimp only [persistenceNestedSubsetTripleMap, persistenceRelativeTripleChainSequenceMap]
  rw [← (relativeChainFunctor K).map_id (TopPair.ofSubset (X := TopCat.of X) A)]
  apply congrArg ((relativeChainFunctor K).map)
  apply persistence_pair_hom_ext
  rfl

lemma persistence_nested_subset_triple_right_map
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) :
    (persistenceNestedSubsetTripleMap K A M N hAM hMN).τ₃ =
      (relativeChainFunctor K).map (persistenceSubsetEnlargementMap M N hMN) := by
  dsimp only [persistenceNestedSubsetTripleMap, persistenceRelativeTripleChainSequenceMap]
  apply congrArg ((relativeChainFunctor K).map)
  apply persistence_pair_hom_ext
  rfl

end HodgeLean.Foundations.QuotientDuality
