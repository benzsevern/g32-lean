import HodgeLean.Foundations.QuotientDuality.ProperCycleInjectiveDerivedSupport

/-! # Actual homology of original derived supported injective sections
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_injective_support_homology_sheaf_derived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance properCycle_injective_support_homology_group_derived :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- Original derived supported homology on a bounded injective model is the homology of the actual ordinary section complex, via the inverse derived unit and original homology comparisons.
Source: properCycle_injective_derived_support_iso; DerivedCategory.Plus.QCompιIso; DerivedCategory.homologyFunctorFactors.
HC no distance; AV milestone no distance. -/
def properCycle_injective_derived_support_homology_iso (X : TopCat.{0}) (S : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (TopCat.Sheaf AddCommGrpCat.{0} X))) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} n).obj
        ((TopCat.Sheaf.derivedClosedSupportSections X S).obj
          (DerivedCategory.Plus.Q.obj
            ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I))) ≅
      (((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
        ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I)).obj).homology n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} n).mapIso
      (properCycle_injective_derived_support_iso X S I) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{0} n).mapIso
      ((DerivedCategory.Plus.QCompιIso AddCommGrpCat.{0}).app
        ((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
          ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I))) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{0} n).app
      (((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
        ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I)).obj)

example (X : TopCat.{0}) (S : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (TopCat.Sheaf AddCommGrpCat.{0} X)))
    (n : ℤ) (b : (((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
      ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj I)).obj).homology n) :
    (properCycle_injective_derived_support_homology_iso X S I n).hom
      ((properCycle_injective_derived_support_homology_iso X S I n).inv b) = b :=
  ConcreteCategory.congr_hom (properCycle_injective_derived_support_homology_iso X S I n).inv_hom_id b

end HodgeLean.Foundations.QuotientDuality
