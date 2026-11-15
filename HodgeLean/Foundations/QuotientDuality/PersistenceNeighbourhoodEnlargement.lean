import HodgeLean.Foundations.QuotientDuality.PersistencePairChainComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceRetractionChainEquiv
import HodgeLean.Foundations.QuotientDuality.PersistenceRelativeDuality

/-! Relative comparison for enlargement of the subspace to its deformation neighbourhood. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

/-- The identity ambient map and the literal subspace inclusion into the neighbourhood. -/
def persistenceNeighbourhoodEnlargement
    (P : TopPair.{0}) (U : TopCat.{0}) (j : P.snd ⟶ U) (k : U ⟶ P.fst)
    (hfactor : j ≫ k = P.map) (hk : Topology.IsEmbedding k) :
    P ⟶ TopPair.of k hk :=
  TopPair.ofHom (𝟙 P.fst) j (by
    change j ≫ k = P.map ≫ 𝟙 P.fst
    rw [hfactor, Category.comp_id])

lemma persistence_neighbourhood_enlargement_relative_chain_quasiIso
    (K : Type) [CommRing K] (P : TopPair.{0}) (U : TopCat.{0})
    (j : P.snd ⟶ U) (k : U ⟶ P.fst) (hfactor : j ≫ k = P.map)
    (hk : Topology.IsEmbedding k) (q : U ⟶ P.snd) (hq : j ≫ q = 𝟙 P.snd)
    (H : TopCat.Homotopy (𝟙 U) (q ≫ j)) :
    QuasiIso ((relativeChainFunctor K).map
      (persistenceNeighbourhoodEnlargement P U j k hfactor hk)) := by
  apply persistence_relative_chain_quasiIso_of_ambient_subspace
  · exact (persistenceRetractionSingularChainHomotopyEquiv K P.snd U j q hq H).quasiIso_hom
  · let F := (AlgebraicTopology.singularChainComplexFunctor.{0}
      (ModuleCat.{0} K)).obj (ModuleCat.of K K)
    change QuasiIso (F.map (𝟙 P.fst))
    rw [F.map_id]
    infer_instance

lemma persistence_neighbourhood_enlargement_relative_cohomology_bijective
    (K : Type) [Field K] (P : TopPair.{0}) (U : TopCat.{0})
    (j : P.snd ⟶ U) (k : U ⟶ P.fst) (hfactor : j ≫ k = P.map)
    (hk : Topology.IsEmbedding k) (q : U ⟶ P.snd) (hq : j ≫ q = 𝟙 P.snd)
    (H : TopCat.Homotopy (𝟙 U) (q ≫ j)) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n
      (persistenceNeighbourhoodEnlargement P U j k hfactor hk)) := by
  exact persistence_relative_cohomology_bijective_of_relative_chain_quasiIso K _
    (persistence_neighbourhood_enlargement_relative_chain_quasiIso K P U j k hfactor hk q hq H) n

end HodgeLean.Foundations.QuotientDuality
