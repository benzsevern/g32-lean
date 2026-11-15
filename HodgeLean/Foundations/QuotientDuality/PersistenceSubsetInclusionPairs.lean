import HodgeLean.Foundations.QuotientDuality.PersistenceEmbeddedPairIso
import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetEnlargement
import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetPairs

/-! The original-locus and actual preimage presentations of neighbourhood pairs. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Identify the actual original-locus inclusion pair with its literal neighbourhood preimage pair. -/
def persistenceSubsetInclusionPairIso
    {X : Type} [TopologicalSpace X] (A M : Set X) (hAM : A ⊆ M) :
    TopPair.of (persistenceSubsetNeighbourhoodInclusion A M hAM)
        (Topology.IsEmbedding.inclusion hAM) ≅
      TopPair.ofSubset (X := TopCat.of M) {m | m.val ∈ A} := by
  let f := persistenceSubsetNeighbourhoodInclusion A M hAM
  have heq : Set.range f = {m : M | m.val ∈ A} := by
    ext m
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hm
      refine ⟨⟨m.val, hm⟩, ?_⟩
      apply Subtype.ext
      rfl
  exact (persistenceEmbeddedPairImageIso f (Topology.IsEmbedding.inclusion hAM)).trans
    (persistenceSubsetPairIso (TopCat.of M) (Set.range f) {m | m.val ∈ A} heq)

end HodgeLean.Foundations.QuotientDuality
