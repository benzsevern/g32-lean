import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Relative homology from the subspace: the five lemma

For a map of pairs `f : P ⟶ Q` whose maps on the subspace and on the ambient space induce
quasi-isomorphisms of singular chains, the map on relative chains is a quasi-isomorphism, so
`f` is bijective on relative homology. This is the five lemma on the long exact sequences of the
two pairs (Hatcher, *Algebraic Topology*, §2.1, p. 129).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

/-- A map of pairs that is a quasi-isomorphism on singular chains of both spaces is a
quasi-isomorphism on relative chains. -/
theorem C_relativeChainMap_quasiIso {P Q : TopPair.{0}} (f : P ⟶ Q)
    (h₁ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (TopPair.Hom.snd f)))
    (h₂ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (TopPair.Hom.fst f))) :
    QuasiIso ((relativeChainFunctor ℚ).map f) := by
  let φ : relativeChainShortComplex ℚ P ⟶ relativeChainShortComplex ℚ Q :=
    { τ₁ := ((chainPairFunctor ℚ).map f).left
      τ₂ := ((chainPairFunctor ℚ).map f).right
      τ₃ := (relativeChainFunctor ℚ).map f
      comm₁₂ := ((chainPairFunctor ℚ).map f).w
      comm₂₃ := (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (relativeChainShortComplex_shortExact ℚ P) (relativeChainShortComplex_shortExact ℚ Q) h₁ h₂

/-- A map of pairs that is a quasi-isomorphism on singular chains of both spaces is bijective on
relative homology. -/
theorem C_relativeHomologyMap_bijective {P Q : TopPair.{0}} (f : P ⟶ Q)
    (h₁ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (TopPair.Hom.snd f)))
    (h₂ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (TopPair.Hom.fst f))) (i : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ i f) := by
  have := C_relativeChainMap_quasiIso f h₁ h₂
  have hiso : IsIso (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map f) i) :=
    inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiso

end HodgeLean.RealDefs
