import HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedSupportSheafCohomology
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsShift

/-! # Original shifted derived support in the literal complementary degree
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_shifted_support_sheaf_derived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance properCycle_shifted_support_group_derived :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- Original supported cohomology in complementary degree is the homology of original derived supported sections of the ambient shifted rational constant object, with the actual single-object and derived-support shift comparisons retained.
Source: properCycle_derived_support_sheaf_cohomology_iso; TopCat.Sheaf.derivedClosedSupportSections_commShift; CategoryTheory.SingleFunctors.shiftIso; CategoryTheory.Functor.shiftIso.
HC no distance; AV milestone no distance. -/
def properCycle_shifted_derived_support_sheaf_iso (X : TopCat.{0}) (S : Closeds X)
    (N n p : ℕ) (h : N = n + p) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (-(n : ℤ))).obj
        ((TopCat.Sheaf.derivedClosedSupportSections X S).obj
          ((DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(N : ℤ))).obj
            (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)))) ≅
      AddCommGrpCat.of (TopCat.Sheaf.supportH X S
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) p) := by
  let A := TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)
  let G := TopCat.Sheaf.derivedClosedSupportSections X S
  let K := (DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj A
  let e := ((DerivedCategory.Plus.singleFunctors (TopCat.Sheaf AddCommGrpCat.{0} X)).shiftIso
    (N : ℤ) (-(N : ℤ)) 0 (by omega)).app A
  exact (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (-(n : ℤ))).mapIso
      (G.mapIso e.symm ≪≫ (G.commShiftIso (N : ℤ)).app K) ≪≫
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} 0).shiftIso
      (N : ℤ) (-(n : ℤ)) (p : ℤ) (by omega)).app (G.obj K) ≪≫
    properCycle_derived_support_sheaf_cohomology_iso X S p

example (X : TopCat.{0}) (S : Closeds X) :
    (properCycle_shifted_derived_support_sheaf_iso X S 4 2 2 rfl).inv ≫
      (properCycle_shifted_derived_support_sheaf_iso X S 4 2 2 rfl).hom = 𝟙 _ :=
  (properCycle_shifted_derived_support_sheaf_iso X S 4 2 2 rfl).inv_hom_id

end HodgeLean.Foundations.QuotientDuality
