import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex

/-! Rational coefficient extension for the actual singular complexes. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

instance persistenceScalarExtensionAdditive
    (K : Type) [CommRing K] [Algebra ℚ K] :
    (ModuleCat.extendScalars (algebraMap ℚ K)).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (ModuleCat.extendScalars (algebraMap ℚ K))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Coefficient extension applied degreewise to the actual chain complexes. -/
abbrev persistenceScalarExtensionChainFunctor
    (K : Type) [CommRing K] [Algebra ℚ K] :
    ChainComplex (ModuleCat.{0} ℚ) ℕ ⥤ ChainComplex (ModuleCat.{0} K) ℕ :=
  (ModuleCat.extendScalars (algebraMap ℚ K)).mapHomologicalComplex (.down ℕ)

instance persistenceScalarExtensionChainPreservesColimits
    (K : Type) [CommRing K] [Algebra ℚ K] :
    PreservesColimitsOfSize.{0, 0} (persistenceScalarExtensionChainFunctor K) where
  preservesColimitsOfShape := by
    intro J hJ
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{0} ℚ) (.down ℕ) n ⋙
        ModuleCat.extendScalars (algebraMap ℚ K))
    infer_instance

end HodgeLean.Foundations.QuotientDuality
