import HodgeLean.Foundations.QuotientDuality.PersistenceNestedTripleObstruction
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Actual global-pair projections controlled by the checked local zero maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_subset_triple_first_homology_map_zero
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) (n : ℕ)
    (hzero : relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion A M N hMN) = 0) :
    HomologicalComplex.homologyMap (persistenceSubsetTripleChainSequence K A M hAM).f n = 0 := by
  let fM := persistenceSubsetNeighbourhoodInclusion A M hAM
  let gM : TopCat.of M ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let fN := persistenceSubsetNeighbourhoodInclusion A N (hAM.trans hMN)
  let gN : TopCat.of N ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hfactor : persistenceTriplePairLeftMap fM gM
      (Topology.IsEmbedding.inclusion hAM) Topology.IsEmbedding.subtypeVal =
      persistenceNestedSubsetPairMap A M N hAM hMN ≫
        persistenceTriplePairLeftMap fN gN (Topology.IsEmbedding.inclusion (hAM.trans hMN))
          Topology.IsEmbedding.subtypeVal := by
    apply persistence_pair_hom_ext
    apply TopCat.ext
    intro m
    rfl
  have hlocal := persistence_nested_subset_pair_relative_homology_zero K A M N hAM hMN n hzero
  have hz : HomologicalComplex.homologyMap ((relativeChainFunctor K).map
      (persistenceNestedSubsetPairMap A M N hAM hMN)) n = 0 := by
    ext u
    exact LinearMap.congr_fun hlocal u
  change HomologicalComplex.homologyMap ((relativeChainFunctor K).map
    (persistenceTriplePairLeftMap fM gM (Topology.IsEmbedding.inclusion hAM)
      Topology.IsEmbedding.subtypeVal)) n = 0
  rw [hfactor, Functor.map_comp, HomologicalComplex.homologyMap_comp, hz, zero_comp]

lemma persistence_subset_enlargement_relative_homology_injective_of_shrink
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) (n : ℕ)
    (hzero : relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion A M N hMN) = 0) :
    Function.Injective (relativeHomologyMap K n (persistenceSubsetEnlargementMap A M hAM)) := by
  let S := persistenceSubsetTripleChainSequence K A M hAM
  let T := S.map (HomologicalComplex.homologyFunctor (ModuleCat.{0} K) (.down ℕ) n)
  have hex : T.Exact :=
    (persistence_subset_triple_chain_sequence_shortExact K A M hAM).homology_exact₂ n
  have hz := persistence_subset_triple_first_homology_map_zero K A M N hAM hMN n hzero
  have hm : Mono T.g := (T.exact_iff_mono hz).mp hex
  have hi : Function.Injective T.g := (ModuleCat.mono_iff_injective T.g).mp hm
  let fM := persistenceSubsetNeighbourhoodInclusion A M hAM
  let gM : TopCat.of M ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hpair : persistenceTriplePairRightMap fM gM (Topology.IsEmbedding.inclusion hAM)
      Topology.IsEmbedding.subtypeVal = persistenceSubsetEnlargementMap A M hAM := by
    apply persistence_pair_hom_ext
    rfl
  change Function.Injective (relativeHomologyMap K n
    (persistenceTriplePairRightMap fM gM (Topology.IsEmbedding.inclusion hAM)
      Topology.IsEmbedding.subtypeVal)) at hi
  rw [hpair] at hi
  exact hi

end HodgeLean.Foundations.QuotientDuality
