import HodgeLean.Foundations.QuotientDuality.PersistenceTripleChains

/-! The actual maps of pairs underlying the singular relative-triple sequence. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The first relative-triple pair map, with the literal second inclusion as ambient map. -/
def persistenceTriplePairLeftMap
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    TopPair.of f hf ⟶ TopPair.of (f ≫ g) (hg.comp hf) :=
  TopPair.ofHom g (𝟙 X) (Category.id_comp _)

/-- The second relative-triple pair map, with the literal identity ambient map. -/
def persistenceTriplePairRightMap
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    TopPair.of (f ≫ g) (hg.comp hf) ⟶ TopPair.of g hg :=
  TopPair.ofHom (𝟙 Z) f (Category.comp_id _).symm

lemma persistence_triple_chain_left_map
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    (relativeChainFunctor K).map (persistenceTriplePairLeftMap f g hf hg) =
      (persistenceTripleChainSequence K f g).f := by
  let F := (AlgebraicTopology.singularChainComplexFunctor.{0}
    (ModuleCat.{0} K)).obj (ModuleCat.of K K)
  change cokernel.map (F.map f) (F.map (f ≫ g)) (F.map (𝟙 X)) (F.map g) (by simp) =
    cokernel.map (F.map f) (F.map (f ≫ g)) (𝟙 _) (F.map g) (by simp)
  apply (cancel_epi (cokernel.π (F.map f))).mp
  simp only [cokernel.map, cokernel.π_desc]

lemma persistence_triple_chain_right_map
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) :
    (relativeChainFunctor K).map (persistenceTriplePairRightMap f g hf hg) =
      (persistenceTripleChainSequence K f g).g := by
  let F := (AlgebraicTopology.singularChainComplexFunctor.{0}
    (ModuleCat.{0} K)).obj (ModuleCat.of K K)
  change cokernel.map (F.map (f ≫ g)) (F.map g) (F.map f) (F.map (𝟙 Z)) (by simp) =
    cokernel.map (F.map (f ≫ g)) (F.map g) (F.map f) (𝟙 _) (by simp)
  apply (cancel_epi (cokernel.π (F.map (f ≫ g)))).mp
  simp only [cokernel.map, cokernel.π_desc, F.map_id]

end HodgeLean.Foundations.QuotientDuality
