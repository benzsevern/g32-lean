import HodgeLean.Foundations.QuotientDuality.PersistenceRelativeDuality
import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! Comparison through the actual short exact singular-chain sequences of pairs. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual map of short exact singular-chain sequences induced by a map of pairs. -/
def persistencePairChainSequenceMap
    (K : Type) [CommRing K] {P Q : TopPair.{0}} (f : P ⟶ Q) :
    relativeChainShortComplex K P ⟶ relativeChainShortComplex K Q where
  τ₁ := ((chainPairFunctor K).map f).left
  τ₂ := ((chainPairFunctor K).map f).right
  τ₃ := (relativeChainFunctor K).map f
  comm₁₂ := ((chainPairFunctor K).map f).w
  comm₂₃ := (TopPair.Homotopy.relativeChainProjection_naturality (R := K) f).symm

lemma persistence_relative_chain_quasiIso_of_ambient_subspace
    (K : Type) [CommRing K] {P Q : TopPair.{0}} (f : P ⟶ Q)
    (hA : QuasiIso ((chainPairFunctor K).map f).left)
    (hX : QuasiIso ((chainPairFunctor K).map f).right) :
    QuasiIso ((relativeChainFunctor K).map f) := by
  exact HomologySequence.quasiIso_τ₃ (persistencePairChainSequenceMap K f)
    (relativeChainShortComplex_shortExact K P) (relativeChainShortComplex_shortExact K Q) hA hX

lemma persistence_relative_cohomology_bijective_of_relative_chain_quasiIso
    (K : Type) [Field K] {P Q : TopPair.{0}} (f : P ⟶ Q)
    (hf : QuasiIso ((relativeChainFunctor K).map f)) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n f) := by
  letI := hf
  have hIso : IsIso ((relativeHomologyFunctor K n).map f) := by
    change IsIso (HomologicalComplex.homologyMap ((relativeChainFunctor K).map f) n)
    infer_instance
  exact persistence_relative_cohomology_bijective_of_homology K f n
    ((ConcreteCategory.isIso_iff_bijective _).mp hIso)

end HodgeLean.Foundations.QuotientDuality
