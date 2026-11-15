import HodgeLean.Foundations.QuotientDuality.PersistenceTripleHomology

/-! Actual compatible maps of relative-triple chain sequences. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The three literal relative-chain maps induced by a compatible diagram of inclusions. -/
def persistenceRelativeTripleChainSequenceMap
    (K : Type) [CommRing K] {X Y Z X' Y' Z' : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
    (hf' : Topology.IsEmbedding f') (hg' : Topology.IsEmbedding g')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z')
    (h₁ : f ≫ b = a ≫ f') (h₂ : g ≫ c = b ≫ g') :
    persistenceRelativeTripleChainSequence K f g hf hg ⟶
      persistenceRelativeTripleChainSequence K f' g' hf' hg' := by
  have htotal : (f ≫ g) ≫ c = a ≫ (f' ≫ g') := by
    calc
      (f ≫ g) ≫ c = f ≫ (g ≫ c) := Category.assoc _ _ _
      _ = f ≫ (b ≫ g') := by rw [h₂]
      _ = (f ≫ b) ≫ g' := (Category.assoc _ _ _).symm
      _ = (a ≫ f') ≫ g' := by rw [h₁]
      _ = a ≫ (f' ≫ g') := Category.assoc _ _ _
  let p₁ : TopPair.of f hf ⟶ TopPair.of f' hf' := TopPair.ofHom b a h₁.symm
  let p₂ : TopPair.of (f ≫ g) (hg.comp hf) ⟶ TopPair.of (f' ≫ g') (hg'.comp hf') :=
    TopPair.ofHom c a htotal.symm
  let p₃ : TopPair.of g hg ⟶ TopPair.of g' hg' := TopPair.ofHom c b h₂.symm
  refine {
    τ₁ := (relativeChainFunctor K).map p₁
    τ₂ := (relativeChainFunctor K).map p₂
    τ₃ := (relativeChainFunctor K).map p₃
    comm₁₂ := ?_
    comm₂₃ := ?_ }
  · change (relativeChainFunctor K).map p₁ ≫
      (relativeChainFunctor K).map (persistenceTriplePairLeftMap f' g' hf' hg') =
      (relativeChainFunctor K).map (persistenceTriplePairLeftMap f g hf hg) ≫
        (relativeChainFunctor K).map p₂
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg ((relativeChainFunctor K).map)
    apply persistence_pair_hom_ext
    exact h₂.symm
  · change (relativeChainFunctor K).map p₂ ≫
      (relativeChainFunctor K).map (persistenceTriplePairRightMap f' g' hf' hg') =
      (relativeChainFunctor K).map (persistenceTriplePairRightMap f g hf hg) ≫
        (relativeChainFunctor K).map p₃
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg ((relativeChainFunctor K).map)
    apply persistence_pair_hom_ext
    exact (Category.comp_id c).trans (Category.id_comp c).symm

lemma persistence_relative_triple_boundary_naturality
    (K : Type) [CommRing K] {X Y Z X' Y' Z' : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
    (hf' : Topology.IsEmbedding f') (hg' : Topology.IsEmbedding g')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z')
    (h₁ : f ≫ b = a ≫ f') (h₂ : g ≫ c = b ≫ g') (n : ℕ) :
    let φ := persistenceRelativeTripleChainSequenceMap K f g f' g' hf hg hf' hg' a b c h₁ h₂
    persistenceRelativeTripleBoundary K f g hf hg n ≫
        HomologicalComplex.homologyMap φ.τ₁ n =
      HomologicalComplex.homologyMap φ.τ₃ (n + 1) ≫
        persistenceRelativeTripleBoundary K f' g' hf' hg' n := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (persistenceRelativeTripleChainSequenceMap K f g f' g' hf hg hf' hg' a b c h₁ h₂)
    (persistence_relative_triple_chain_sequence_shortExact K f g hf hg)
    (persistence_relative_triple_chain_sequence_shortExact K f' g' hf' hg') (n + 1) n (by
      simp [ComplexShape.down_Rel])

end HodgeLean.Foundations.QuotientDuality
