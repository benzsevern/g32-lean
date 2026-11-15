import HodgeLean.Foundations.QuotientDuality.PersistenceCokernelFactor
import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence

/-! Actual singular relative-chain sequences for composable pair inclusions. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The cokernel sequence on the actual singular-chain images of the three inclusions. -/
def persistenceTripleChainSequence
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex (ChainComplex (ModuleCat.{0} K) ℕ) :=
  let F := (AlgebraicTopology.singularChainComplexFunctor.{0}
    (ModuleCat.{0} K)).obj (ModuleCat.of K K)
  persistenceCokernelFactorSequence (F.map f) (F.map g) (F.map (f ≫ g)) (F.map_comp f g).symm

lemma persistence_triple_chain_sequence_shortExact
    (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Topology.IsEmbedding g) : (persistenceTripleChainSequence K f g).ShortExact := by
  let F := (AlgebraicTopology.singularChainComplexFunctor.{0}
    (ModuleCat.{0} K)).obj (ModuleCat.of K K)
  letI : Mono g := (TopCat.mono_iff_injective g).mpr hg.injective
  haveI : Mono (F.map g) := by apply Functor.map_mono
  exact persistence_cokernel_factor_sequence_shortExact
    (F.map f) (F.map g) (F.map (f ≫ g)) (F.map_comp f g).symm

end HodgeLean.Foundations.QuotientDuality
