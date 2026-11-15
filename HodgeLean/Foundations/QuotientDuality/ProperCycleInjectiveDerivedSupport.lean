import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedConstantInjective

/-! # Actual computation of original derived support on bounded injective complexes
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_injective_support_sheaf_derived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance properCycle_injective_support_group_derived :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- On an actual bounded complex of injective sheaves, the inverse of the original right-derived unit identifies original derived supported sections with ordinary supported sections of that same complex.
Source: CategoryTheory.Functor.rightDerivedFunctorPlusUnit; Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.
HC no distance; AV milestone no distance. -/
def properCycle_injective_derived_support_iso (X : TopCat.{0}) (S : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (TopCat.Sheaf AddCommGrpCat.{0} X))) :
    (TopCat.Sheaf.derivedClosedSupportSections X S).obj
        (DerivedCategory.Plus.Q.obj
          ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I)) ≅
      DerivedCategory.Plus.Q.obj
        ((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
          ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I)) :=
  (asIso ((TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I))).symm

example (X : TopCat.{0}) (S : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (TopCat.Sheaf AddCommGrpCat.{0} X))) :
    (TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I) ≫
      (properCycle_injective_derived_support_iso X S I).hom = 𝟙 _ :=
  (asIso ((TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I))).hom_inv_id

end HodgeLean.Foundations.QuotientDuality
