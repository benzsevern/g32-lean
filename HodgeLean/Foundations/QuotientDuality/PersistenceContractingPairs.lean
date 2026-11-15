import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! Relative homology of contracting singleton pairs. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_full_pair_relative_homology_isZero
    (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    IsZero (RelativeHomology K (TopPair.ofSubset (Set.univ : Set X)) n) := by
  let P := TopPair.ofSubset (Set.univ : Set X)
  haveI : IsIso P.map :=
    (TopCat.isIso_iff_isHomeomorph P.map).mpr (Homeomorph.Set.univ X).isHomeomorph
  haveI : IsIso ((chainPairFunctor K).obj P).hom := by
    change IsIso (((AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} K)).obj (ModuleCat.of K K)).map P.map)
    infer_instance
  have hz : IsZero ((relativeChainFunctor K).obj P) :=
    isZero_cokernel_of_epi ((chainPairFunctor K).obj P).hom
  exact (homologyFunctor (ModuleCat K) (ComplexShape.down ℕ) n).map_isZero hz

lemma persistence_relative_homology_isZero_of_pair_map_isIso
    (K : Type) [CommRing K] (P : TopPair.{0}) [IsIso P.map] (n : ℕ) :
    IsZero (RelativeHomology K P n) := by
  haveI : IsIso ((chainPairFunctor K).obj P).hom := by
    change IsIso (((AlgebraicTopology.singularChainComplexFunctor.{0}
      (ModuleCat.{0} K)).obj (ModuleCat.of K K)).map P.map)
    infer_instance
  have hz : IsZero ((relativeChainFunctor K).obj P) :=
    isZero_cokernel_of_epi ((chainPairFunctor K).obj P).hom
  exact (homologyFunctor (ModuleCat K) (ComplexShape.down ℕ) n).map_isZero hz

end HodgeLean.Foundations.QuotientDuality
