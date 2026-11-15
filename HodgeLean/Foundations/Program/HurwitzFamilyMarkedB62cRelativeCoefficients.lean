import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular

theorem b6m_relativeChainMap_quasiIso (R : Type) [CommRing R]
    {P Q : TopPair.{0}} (f : P ⟶ Q)
    (h₁ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map (TopPair.Hom.snd f)))
    (h₂ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map (TopPair.Hom.fst f))) :
    QuasiIso ((relativeChainFunctor R).map f) := by
  let φ : relativeChainShortComplex R P ⟶ relativeChainShortComplex R Q :=
    { τ₁ := ((chainPairFunctor R).map f).left
      τ₂ := ((chainPairFunctor R).map f).right
      τ₃ := (relativeChainFunctor R).map f
      comm₁₂ := ((chainPairFunctor R).map f).w
      comm₂₃ := (TopPair.Homotopy.relativeChainProjection_naturality (R := R) f).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (relativeChainShortComplex_shortExact R P) (relativeChainShortComplex_shortExact R Q) h₁ h₂

theorem b6m_relativeHomologyMap_bijective (R : Type) [CommRing R]
    {P Q : TopPair.{0}} (f : P ⟶ Q)
    (h₁ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map (TopPair.Hom.snd f)))
    (h₂ : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map (TopPair.Hom.fst f))) (i : ℕ) :
    Function.Bijective (relativeHomologyMap R i f) := by
  have := b6m_relativeChainMap_quasiIso R f h₁ h₂
  have hiso : IsIso (HomologicalComplex.homologyMap ((relativeChainFunctor R).map f) i) :=
    inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiso

theorem b6m_relativeHomology_isZero_of_absolute_and_subspace
    (R : Type) [CommRing R] (P : TopPair.{0}) (n : ℕ)
    (hX : IsZero (Homology R P.fst (n + 1)))
    (hA : IsZero (Homology R P.snd n)) :
    IsZero (RelativeHomology R P (n + 1)) := by
  exact ((relativeChainShortComplex_shortExact R P).homology_exact₃
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))).isZero_of_both_isZero hX hA

theorem b6m_relativeHomology_empty_support_isZero
    (R : Type) [CommRing R] (M : Type) [TopologicalSpace M] (i : ℕ) :
    IsZero (RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (∅ : Set M)ᶜ) i) := by
  let P := TopPair.ofSubset (X := TopCat.of M) (∅ : Set M)ᶜ
  have : IsIso P.map := by
    refine ⟨TopCat.ofHom ⟨fun y => ⟨y, Set.notMem_empty y⟩, by fun_prop⟩, ?_, ?_⟩
    · ext y; rfl
    · ext y; rfl
  have hf : IsIso (relativeChainShortComplex R P).f := by
    change IsIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map P.map)
    infer_instance
  exact (HomologicalComplex.homologyFunctor _ _ i).map_isZero
    (((relativeChainShortComplex_shortExact R P).isIso_f_iff).mp hf)

end HodgeLean.Foundations.Program
