import HodgeLean.Foundations.QuotientDuality.PersistenceTriplePairMaps
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! The actual short exact relative-chain sequence of a topological triple. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal three relative-chain objects and the maps induced by the actual pair morphisms. -/
def persistenceRelativeTripleChainSequence
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    ShortComplex (ChainComplex (ModuleCat.{0} K) ℕ) where
  X₁ := (relativeChainFunctor K).obj (TopPair.of f hf)
  X₂ := (relativeChainFunctor K).obj (TopPair.of (f ≫ g) (hg.comp hf))
  X₃ := (relativeChainFunctor K).obj (TopPair.of g hg)
  f := (relativeChainFunctor K).map (persistenceTriplePairLeftMap f g hf hg)
  g := (relativeChainFunctor K).map (persistenceTriplePairRightMap f g hf hg)
  zero := by
    rw [persistence_triple_chain_left_map, persistence_triple_chain_right_map]
    exact (persistenceTripleChainSequence K f g).zero

lemma persistence_relative_triple_chain_sequence_shortExact
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    (persistenceRelativeTripleChainSequence K f g hf hg).ShortExact := by
  let e : persistenceRelativeTripleChainSequence K f g hf hg ≅
      persistenceTripleChainSequence K f g :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change (𝟙 _) ≫ (persistenceTripleChainSequence K f g).f =
          (relativeChainFunctor K).map (persistenceTriplePairLeftMap f g hf hg) ≫ (𝟙 _)
        rw [Category.id_comp, Category.comp_id, persistence_triple_chain_left_map])
      (by
        change (𝟙 _) ≫ (persistenceTripleChainSequence K f g).g =
          (relativeChainFunctor K).map (persistenceTriplePairRightMap f g hf hg) ≫ (𝟙 _)
        rw [Category.id_comp, Category.comp_id, persistence_triple_chain_right_map])
  exact ShortComplex.shortExact_of_iso e.symm (persistence_triple_chain_sequence_shortExact K f g hg)

end HodgeLean.Foundations.QuotientDuality
