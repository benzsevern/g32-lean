import HodgeLean.Foundations.QuotientDuality.ProperCycleConstantBoundedResolution
import HodgeLean.Foundations.QuotientDuality.ProperCycleInjectiveDerivedSupportHomology
import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel

/-! # Original derived supported cohomology agrees with actual relative sheaf cohomology
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_supported_cohomology_sheaf_derived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance properCycle_supported_cohomology_group_derived :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- The original derived supported sections of the rational constant object compute the original relative sheaf cohomology with the same literal support, using the fixed rational injective resolution and its actual augmentation.
Source: properCycle_constant_bounded_resolution_iso; properCycle_injective_derived_support_homology_iso; TopCat.Sheaf.relHAddEquivSupportedSectionsHomology.
HC no distance; AV milestone no distance. -/
def properCycle_derived_support_sheaf_cohomology_iso (X : TopCat.{0}) (S : Closeds X) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (n : ℤ)).obj
        ((TopCat.Sheaf.derivedClosedSupportSections X S).obj
          ((DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
            (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)))) ≅
      AddCommGrpCat.of (TopCat.Sheaf.supportH X S
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) n) := by
  letI := properCycle_constant_injective_augmentation_quasiIso X
  letI : (rationalConstantInjectiveComplex X).IsKInjective :=
    CochainComplex.isKInjective_of_injective _ 0
  let e := TopCat.Sheaf.relHAddEquivSupportedSectionsHomology X S.compl ⊤ S.compl
    (by simp) (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))
    (rationalConstantInjectiveComplex X) (properCycle_constant_injective_augmentation X) n
  exact (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (n : ℤ)).mapIso
      ((TopCat.Sheaf.derivedClosedSupportSections X S).mapIso
        (properCycle_constant_bounded_resolution_iso X)) ≪≫
    properCycle_injective_derived_support_homology_iso X S
      (properCycle_bounded_constant_injective X) (n : ℤ) ≪≫
    e.symm.toAddCommGrpIso

example (X : TopCat.{0}) (S : Closeds X) (n : ℕ) :
    (properCycle_derived_support_sheaf_cohomology_iso X S n).inv ≫
      (properCycle_derived_support_sheaf_cohomology_iso X S n).hom = 𝟙 _ :=
  (properCycle_derived_support_sheaf_cohomology_iso X S n).inv_hom_id

end HodgeLean.Foundations.QuotientDuality
