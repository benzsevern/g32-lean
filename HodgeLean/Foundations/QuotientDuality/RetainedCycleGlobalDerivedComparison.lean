import HodgeLean.Foundations.QuotientDuality.RetainedCycleDerivedHomComparison
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections

noncomputable section
open CategoryTheory Limits CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance retainedGlobalDerivedHasDerivedCategory (X : TopCat.{0}) : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

/-- The canonical comparison from ordinary global-section cohomology to derived global morphisms. -/
def retainedGlobalSectionsDerivedComparison (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) (n : ℤ) :
    (TopCat.Sheaf.globalSectionsComplexInt X K).homology n →+
      (DerivedCategory.Q.obj (TopCat.Sheaf.integerConstantSingleComplex X) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) :=
  (retainedHomCohomologyDerivedComparison (TopCat.Sheaf.integerConstantSingleComplex X) K n).comp
    ((homologyAddEquiv (TopCat.Sheaf.integerConstantSingleComplex X) K n).toAddMonoidHom.comp
      (HomologicalComplex.homologyMapIso
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections X K).symm n).addCommGroupIsoToAddEquiv.toAddMonoidHom)

/-- The canonical global-section comparison is bijective for a K-injective sheaf complex. -/
theorem retained_global_sections_derived_comparison_bijective_of_kInjective
    (X : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ)
    [K.IsKInjective] (n : ℤ) :
    Function.Bijective (retainedGlobalSectionsDerivedComparison X K n) :=
  (retained_hom_cohomology_derived_comparison_bijective _ K n).comp
    ((homologyAddEquiv (TopCat.Sheaf.integerConstantSingleComplex X) K n).bijective.comp
      (HomologicalComplex.homologyMapIso
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections X K).symm n).addCommGroupIsoToAddEquiv.bijective)

end HodgeLean.Foundations.QuotientDuality
