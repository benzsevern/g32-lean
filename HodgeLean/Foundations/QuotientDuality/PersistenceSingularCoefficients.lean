import HodgeLean.Foundations.QuotientDuality.PersistenceScalarExtension
import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology

/-! Natural coefficient comparison for the actual singular-chain functors. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Extension of the rational coefficient module is the specified coefficient ring. -/
def persistenceScalarExtensionUnitIso
    (K : Type) [CommRing K] [Algebra ℚ K] :
    (ModuleCat.extendScalars (algebraMap ℚ K)).obj (ModuleCat.of ℚ ℚ) ≅ ModuleCat.of K K := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid ℚ K K).toModuleIso

/-- Singular chains commute naturally with extension of the rational coefficients. -/
def persistenceSingularCoefficientIso
    (K : Type) [CommRing K] [Algebra ℚ K] :
    ((AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)) ⋙ persistenceScalarExtensionChainFunctor K ≅
      (AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} K)).obj
        (ModuleCat.of K K) :=
  (isoWhiskerLeft TopCat.toSSet
    (SSet.chainComplexFunctorObjCompMapIso (ModuleCat.extendScalars (algebraMap ℚ K))
      (ModuleCat.of ℚ ℚ))) ≪≫
    (isoWhiskerLeft TopCat.toSSet
      ((SSet.chainComplexFunctor (ModuleCat.{0} K)).mapIso (persistenceScalarExtensionUnitIso K)))

end HodgeLean.Foundations.QuotientDuality
