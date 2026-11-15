import HodgeLean.Foundations.QuotientDuality.PersistenceSingularCoefficients
import HodgeLean.Foundations.QuotientDuality.PersistenceCoefficientCokernel

/-! Natural coefficient comparison for the actual relative singular-chain functors. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Coefficient extension respects the literal inclusion of subspace chains. -/
def persistenceChainPairCoefficientIso
    (K : Type) [CommRing K] [Algebra ℚ K] :
    chainPairFunctor ℚ ⋙ (persistenceScalarExtensionChainFunctor K).mapArrow ≅
      chainPairFunctor K :=
  isoWhiskerLeft (MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤)
    ((Functor.mapArrowFunctor TopCat (ChainComplex (ModuleCat.{0} K) ℕ)).mapIso
      (persistenceSingularCoefficientIso K))

/-- Relative chains commute naturally with actual extension of the rational coefficients. -/
def persistenceRelativeCoefficientIso
    (K : Type) [CommRing K] [Algebra ℚ K] :
    relativeChainFunctor ℚ ⋙ persistenceScalarExtensionChainFunctor K ≅ relativeChainFunctor K :=
  (isoWhiskerLeft (chainPairFunctor ℚ)
    (persistenceCokernelCoefficientIso (persistenceScalarExtensionChainFunctor K))) ≪≫
    (isoWhiskerRight (persistenceChainPairCoefficientIso K)
      (Limits.coker (C := ChainComplex (ModuleCat.{0} K) ℕ)))

end HodgeLean.Foundations.QuotientDuality
