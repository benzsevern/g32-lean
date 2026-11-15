import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetInclusionPairs
import HodgeLean.Foundations.QuotientDuality.PersistenceNeighbourhoodHomologyZero

/-! Actual nested neighbourhood pair maps in both subspace presentations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual neighbourhood inclusion with the original locus as its common subspace. -/
def persistenceNestedSubsetPairMap
    {X : Type} [TopologicalSpace X] (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) :
    TopPair.of (persistenceSubsetNeighbourhoodInclusion A M hAM)
        (Topology.IsEmbedding.inclusion hAM) ⟶
      TopPair.of (persistenceSubsetNeighbourhoodInclusion A N (hAM.trans hMN))
        (Topology.IsEmbedding.inclusion (hAM.trans hMN)) :=
  TopPair.ofHom (persistenceSubsetNeighbourhoodInclusion M N hMN) (𝟙 (TopCat.of A)) (by
    apply TopCat.ext
    intro a
    rfl)

lemma persistence_nested_subset_pair_presentation_square
    {X : Type} [TopologicalSpace X] (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) :
    (persistenceSubsetInclusionPairIso A M hAM).hom ≫
        persistenceNeighbourhoodPairInclusion A M N hMN =
      persistenceNestedSubsetPairMap A M N hAM hMN ≫
        (persistenceSubsetInclusionPairIso A N (hAM.trans hMN)).hom := by
  apply persistence_pair_hom_ext
  apply TopCat.ext
  intro m
  rfl

lemma persistence_nested_subset_pair_relative_homology_zero
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) (n : ℕ)
    (hzero : relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion A M N hMN) = 0) :
    relativeHomologyMap K n (persistenceNestedSubsetPairMap A M N hAM hMN) = 0 := by
  let eN := persistenceSubsetInclusionPairIso A N (hAM.trans hMN)
  have hIso : IsIso ((relativeHomologyFunctor K n).map eN.hom) := by infer_instance
  have hb : Function.Bijective (relativeHomologyMap K n eN.hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hIso
  have h := congrArg (relativeHomologyMap K n)
    (persistence_nested_subset_pair_presentation_square A M N hAM hMN)
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp] at h
  ext u
  apply hb.injective
  simp only [LinearMap.zero_apply, map_zero]
  have hv := LinearMap.congr_fun h u
  simpa only [LinearMap.comp_apply, hzero, LinearMap.zero_apply] using hv.symm

end HodgeLean.Foundations.QuotientDuality
