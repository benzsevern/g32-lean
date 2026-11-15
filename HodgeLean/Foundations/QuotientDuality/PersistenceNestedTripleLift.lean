import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetTripleProjection

/-! Actual enlarged-pair classes lifted through the controlled nested relative triples. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_nested_triple_relative_homology_lift
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) (n : ℕ)
    (hzero : ∀ k : ℕ, relativeHomologyMap K k
      (persistenceNeighbourhoodPairInclusion A M N hMN) = 0)
    (u : RelativeHomology K (TopPair.ofSubset (X := TopCat.of X) M) n) :
    ∃ v : RelativeHomology K (TopPair.ofSubset (X := TopCat.of X) A) n,
      relativeHomologyMap K n (persistenceSubsetEnlargementMap A N (hAM.trans hMN)) v =
        relativeHomologyMap K n (persistenceSubsetEnlargementMap M N hMN) u := by
  cases n with
  | zero =>
    exact persistence_subset_enlargement_relative_homology_zero_surjective K A N (hAM.trans hMN)
      (relativeHomologyMap K 0 (persistenceSubsetEnlargementMap M N hMN) u)
  | succ n =>
    let S := persistenceSubsetTripleChainSequence K A N (hAM.trans hMN)
    let hS := persistence_subset_triple_chain_sequence_shortExact K A N (hAM.trans hMN)
    let δ := hS.δ (n + 1) n (by simp [ComplexShape.down_Rel])
    have hy : δ (relativeHomologyMap K (n + 1) (persistenceSubsetEnlargementMap M N hMN) u) = 0 := by
      have h := persistence_nested_triple_boundary_comp_zero K A M N hAM hMN n (hzero n)
      exact congrArg (fun k => k u) h
    have hex := hS.homology_exact₃ (n + 1) n (by simp [ComplexShape.down_Rel])
    obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex
      (relativeHomologyMap K (n + 1) (persistenceSubsetEnlargementMap M N hMN) u) hy
    refine ⟨v, ?_⟩
    change relativeHomologyMap K (n + 1)
      (persistenceTriplePairRightMap
        (persistenceSubsetNeighbourhoodInclusion A N (hAM.trans hMN))
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of N ⟶ TopCat.of X)
        (Topology.IsEmbedding.inclusion (hAM.trans hMN)) Topology.IsEmbedding.subtypeVal) v = _ at hv
    rw [persistence_subset_triple_pair_projection] at hv
    exact hv

end HodgeLean.Foundations.QuotientDuality
