import HodgeLean.Foundations.QuotientDuality.ProperCycleQuotientSequence
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-! # Actual quotient chain sequence of three nested spaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable (X : TopCat) (A B : Set X) (hAB : A ⊆ B)

/-- The pair with literal smaller space `A` and ambient space `B`.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains of triples.
HC no distance; AV milestone no distance. -/
def properCycle_nested_pair : TopPair :=
  TopPair.of (TopCat.ofHom ⟨Set.inclusion hAB, continuous_subtype_val.subtype_mk _⟩)
    (Topology.IsEmbedding.inclusion hAB)

/-- The canonical composite of the three actual singular chain inclusions.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains of triples.
HC no distance; AV milestone no distance. -/
lemma properCycle_nested_chain_composite :
    ((chainPairFunctor ℚ).obj (properCycle_nested_pair X A B hAB)).hom ≫
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset B)).hom =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom := by
  change ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ ≫
    ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ = _
  exact (Functor.map_comp _ _ _).symm

/-- The actual relative chain quotient sequence for three nested spaces.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains of triples.
HC no distance; AV milestone no distance. -/
def properCycle_relative_triple_sequence : ShortComplex (ChainCategory ℚ) :=
  properCycle_cokernel_factorization_sequence
    ((chainPairFunctor ℚ).obj (properCycle_nested_pair X A B hAB)).hom
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset B)).hom
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom
    (properCycle_nested_chain_composite X A B hAB)

/-- The actual chain sequence of a triple is short exact.
Source: Hatcher, Algebraic Topology, section 2.1, exactness for triples.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triple_sequence_shortExact :
    (properCycle_relative_triple_sequence X A B hAB).ShortExact := by
  letI : Mono ((chainPairFunctor ℚ).obj (TopPair.ofSubset B)).hom :=
    relativeChainMap_mono ℚ (TopPair.ofSubset B)
  unfold properCycle_relative_triple_sequence
  exact properCycle_cokernel_factorization_sequence_shortExact _ _ _ _

/-- The actual inclusion of the inner relative pair into the ambient relative pair.
Source: Hatcher, Algebraic Topology, section 2.1, maps of triples.
HC no distance; AV milestone no distance. -/
def properCycle_relative_triple_first :
    properCycle_nested_pair X A B hAB ⟶ TopPair.ofSubset A :=
  TopPair.ofHom (TopPair.ofSubset B).map (𝟙 _) (by ext; rfl)

/-- The actual change from the smaller to the larger relative subspace.
Source: Hatcher, Algebraic Topology, section 2.1, maps of triples.
HC no distance; AV milestone no distance. -/
def properCycle_relative_triple_second :
    TopPair.ofSubset A ⟶ TopPair.ofSubset B :=
  TopPair.ofHom (𝟙 X) (properCycle_nested_pair X A B hAB).map (by ext; rfl)

/-- The first quotient-sequence arrow is the literal relative chain map.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative chains.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triple_first_map :
    (properCycle_relative_triple_sequence X A B hAB).f =
      (relativeChainFunctor ℚ).map (properCycle_relative_triple_first X A B hAB) := by
  apply (cancel_epi (cokernel.π
    ((chainPairFunctor ℚ).obj (properCycle_nested_pair X A B hAB)).hom)).mp
  simp [properCycle_relative_triple_sequence, properCycle_cokernel_factorization_sequence,
    relativeChainFunctor, chainPairFunctor, properCycle_relative_triple_first]
  rfl

/-- The second quotient-sequence arrow is the literal relative chain map.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative chains.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triple_second_map :
    (properCycle_relative_triple_sequence X A B hAB).g =
      (relativeChainFunctor ℚ).map (properCycle_relative_triple_second X A B hAB) := by
  apply (cancel_epi (cokernel.π
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom)).mp
  simp [properCycle_relative_triple_sequence, properCycle_cokernel_factorization_sequence,
    relativeChainFunctor, chainPairFunctor, properCycle_relative_triple_second]
  have hi := ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map_id X
  exact (Category.id_comp _).symm.trans
    (congrArg (fun t => t ≫ cokernel.π ((chainPairFunctor ℚ).obj (TopPair.ofSubset B)).hom) hi.symm)

end HodgeLean.Foundations.QuotientDuality
