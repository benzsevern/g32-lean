import HodgeLean.Foundations.QuotientDuality.PersistenceRelativeTriple

/-! Exact homology sequences on the actual relative-triple chain maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Homology of the literal short exact relative-chain triple sequence. -/
def persistenceRelativeTripleHomologySequence
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (n : ℕ) :
    ShortComplex (ModuleCat.{0} K) :=
  (persistenceRelativeTripleChainSequence K f g hf hg).map
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} K) (.down ℕ) n)

lemma persistence_relative_triple_homology_sequence_exact
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (n : ℕ) :
    (persistenceRelativeTripleHomologySequence K f g hf hg n).Exact :=
  (persistence_relative_triple_chain_sequence_shortExact K f g hf hg).homology_exact₂ n

/-- The actual relative-triple connecting morphism in consecutive nonnegative degrees. -/
def persistenceRelativeTripleBoundary
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (n : ℕ) :
    RelativeHomology K (TopPair.of g hg) (n + 1) ⟶ RelativeHomology K (TopPair.of f hf) n :=
  (persistence_relative_triple_chain_sequence_shortExact K f g hf hg).δ (n + 1) n (by
    simp [ComplexShape.down_Rel])

/-- The actual six-term relative-triple homology sequence in consecutive natural degrees. -/
def persistenceRelativeTripleSixTermSequence
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} K) 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (persistence_relative_triple_chain_sequence_shortExact K f g hf hg) (n + 1) n (by
      simp [ComplexShape.down_Rel])

lemma persistence_relative_triple_six_term_sequence_exact
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (n : ℕ) :
    (persistenceRelativeTripleSixTermSequence K f g hf hg n).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (persistence_relative_triple_chain_sequence_shortExact K f g hf hg) (n + 1) n (by
      simp [ComplexShape.down_Rel])

lemma persistence_relative_triple_homology_zero_surjective
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    Function.Surjective (relativeHomologyMap K 0 (persistenceTriplePairRightMap f g hf hg)) := by
  let S := persistenceRelativeTripleChainSequence K f g hf hg
  have hS := persistence_relative_triple_chain_sequence_shortExact K f g hf hg
  haveI : Epi S.g := hS.epi_g
  have hepi : Epi (HomologicalComplex.homologyMap S.g 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by
      intro j
      simp [ComplexShape.down_Rel])
  exact (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap S.g 0)).mp hepi

end HodgeLean.Foundations.QuotientDuality
