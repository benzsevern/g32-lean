import HodgeLean.Foundations.QuotientDuality.PersistenceNestedTriples

/-! Boundary calculations for the actual nested relative triples. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_nested_triple_boundary_comp_zero
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) (n : ℕ)
    (hzero : relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion A M N hMN) = 0) :
    HomologicalComplex.homologyMap ((relativeChainFunctor K).map
        (persistenceSubsetEnlargementMap M N hMN)) (n + 1) ≫
      (persistence_subset_triple_chain_sequence_shortExact K A N (hAM.trans hMN)).δ
        (n + 1) n (by simp [ComplexShape.down_Rel]) = 0 := by
  let φ := persistenceNestedSubsetTripleMap K A M N hAM hMN
  have h := HomologicalComplex.HomologySequence.δ_naturality φ
    (persistence_subset_triple_chain_sequence_shortExact K A M hAM)
    (persistence_subset_triple_chain_sequence_shortExact K A N (hAM.trans hMN))
    (n + 1) n (by simp [ComplexShape.down_Rel])
  dsimp only [φ] at h
  rw [persistence_nested_subset_triple_left_map, persistence_nested_subset_triple_right_map] at h
  have hlocal := persistence_nested_subset_pair_relative_homology_zero K A M N hAM hMN n hzero
  have hz : HomologicalComplex.homologyMap ((relativeChainFunctor K).map
      (persistenceNestedSubsetPairMap A M N hAM hMN)) n = 0 := by
    ext u
    exact LinearMap.congr_fun hlocal u
  rw [hz, comp_zero] at h
  exact h.symm

end HodgeLean.Foundations.QuotientDuality
