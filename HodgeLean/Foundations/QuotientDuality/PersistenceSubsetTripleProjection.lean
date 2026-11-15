import HodgeLean.Foundations.QuotientDuality.PersistenceNestedTripleProjection

/-! Actual pair projections in subset triples and their zero-degree surjectivity. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_subset_triple_pair_projection
    {X : Type} [TopologicalSpace X] (A M : Set X) (hAM : A ⊆ M) :
    persistenceTriplePairRightMap (persistenceSubsetNeighbourhoodInclusion A M hAM)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of M ⟶ TopCat.of X)
        (Topology.IsEmbedding.inclusion hAM) Topology.IsEmbedding.subtypeVal =
      persistenceSubsetEnlargementMap A M hAM := by
  apply persistence_pair_hom_ext
  rfl

lemma persistence_subset_enlargement_relative_homology_zero_surjective
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M : Set X) (hAM : A ⊆ M) :
    Function.Surjective (relativeHomologyMap K 0 (persistenceSubsetEnlargementMap A M hAM)) := by
  have h := persistence_relative_triple_homology_zero_surjective K
    (persistenceSubsetNeighbourhoodInclusion A M hAM)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of M ⟶ TopCat.of X)
    (Topology.IsEmbedding.inclusion hAM) Topology.IsEmbedding.subtypeVal
  rw [persistence_subset_triple_pair_projection] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
