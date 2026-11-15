import HodgeLean.Foundations.QuotientDuality.PersistenceTripleNaturality
import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetInclusionPairs
import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseNeighbourhood
import HodgeLean.Foundations.QuotientDuality.PersistenceGoodPairCollapse

/-! The actual collapse diagram of relative triples. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal triple of the locus, its neighbourhood, and the ambient space. -/
def persistenceSubsetTripleChainSequence
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M : Set X) (hAM : A ⊆ M) : ShortComplex (ChainComplex (ModuleCat.{0} K) ℕ) :=
  persistenceRelativeTripleChainSequence K (persistenceSubsetNeighbourhoodInclusion A M hAM)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of M ⟶ TopCat.of X)
    (Topology.IsEmbedding.inclusion hAM) Topology.IsEmbedding.subtypeVal

/-- The actual relative-triple chain map induced by the literal locus collapse. -/
def persistenceCollapseSubsetTripleMap
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M : Set X) (hAM : A ⊆ M) (a : X) (ha : a ∈ A) :
    persistenceSubsetTripleChainSequence K A M hAM ⟶
      persistenceSubsetTripleChainSequence K
        ({Quotient.mk (persistenceCollapseSetoid A) a})
        ((Quotient.mk (persistenceCollapseSetoid A)) '' M)
        (by
          intro z hz
          rcases Set.mem_singleton_iff.mp hz with rfl
          exact ⟨a, hAM ha, rfl⟩) := by
  let Q := Quotient (persistenceCollapseSetoid A)
  let q := Quotient.mk (persistenceCollapseSetoid A)
  let P : Set Q := {q a}
  let M' := q '' M
  have hPM : P ⊆ M' := by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact ⟨a, hAM ha, rfl⟩
  let f := persistenceSubsetNeighbourhoodInclusion A M hAM
  let g : TopCat.of M ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let f' := persistenceSubsetNeighbourhoodInclusion P M' hPM
  let g' : TopCat.of M' ⟶ TopCat.of Q := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let aMap : TopCat.of A ⟶ TopCat.of P :=
    TopCat.ofHom (ContinuousMap.const A (⟨q a, rfl⟩ : P))
  let bMap : TopCat.of M ⟶ TopCat.of M' :=
    TopCat.ofHom (persistenceCollapseNeighbourhoodProjection A M)
  let cMap : TopCat.of X ⟶ TopCat.of Q := TopCat.ofHom ⟨q, continuous_quotient_mk'⟩
  have h₁ : f ≫ bMap = aMap ≫ f' := by
    apply TopCat.ext
    intro z
    apply Subtype.ext
    exact Quotient.sound (Or.inr ⟨z.property, ha⟩)
  have h₂ : g ≫ cMap = bMap ≫ g' := by
    apply TopCat.ext
    intro z
    rfl
  exact persistenceRelativeTripleChainSequenceMap K f g f' g'
    (Topology.IsEmbedding.inclusion hAM) Topology.IsEmbedding.subtypeVal
    (Topology.IsEmbedding.inclusion hPM) Topology.IsEmbedding.subtypeVal
    aMap bMap cMap h₁ h₂

lemma persistence_subset_triple_chain_sequence_shortExact
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M : Set X) (hAM : A ⊆ M) :
    (persistenceSubsetTripleChainSequence K A M hAM).ShortExact :=
  persistence_relative_triple_chain_sequence_shortExact K
    (persistenceSubsetNeighbourhoodInclusion A M hAM)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of M ⟶ TopCat.of X)
    (Topology.IsEmbedding.inclusion hAM) Topology.IsEmbedding.subtypeVal

lemma persistence_collapse_subset_triple_middle_map
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M : Set X) (hAM : A ⊆ M) (a : X) (ha : a ∈ A) :
    (persistenceCollapseSubsetTripleMap K A M hAM a ha).τ₂ =
      (relativeChainFunctor K).map (persistenceCollapseLocusPairMap A a ha) := by
  dsimp only [persistenceCollapseSubsetTripleMap, persistenceRelativeTripleChainSequenceMap]
  apply congrArg ((relativeChainFunctor K).map)
  apply persistence_pair_hom_ext
  rfl

lemma persistence_collapse_subset_triple_right_map
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M : Set X) (hAM : A ⊆ M) (a : X) (ha : a ∈ A) :
    (persistenceCollapseSubsetTripleMap K A M hAM a ha).τ₃ =
      (relativeChainFunctor K).map (persistenceCollapseNeighbourhoodPairMap A M) := by
  dsimp only [persistenceCollapseSubsetTripleMap, persistenceRelativeTripleChainSequenceMap]
  apply congrArg ((relativeChainFunctor K).map)
  apply persistence_pair_hom_ext
  rfl

end HodgeLean.Foundations.QuotientDuality
