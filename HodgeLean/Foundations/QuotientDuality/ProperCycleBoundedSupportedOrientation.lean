import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedDerivedOrientation
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSections

/-! # Original derived supported orientation of the actual bounded chain sheaf
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_supported_derived_sheaf_category (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance properCycle_supported_derived_group_category :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- Applying the original derived supported-section functor retains the specified ambient orientation on the actual bounded chain sheaf object.
Source: properCycle_bounded_derived_orientation; TopCat.Sheaf.derivedClosedSupportSections.
HC no distance; AV milestone no distance. -/
def properCycle_bounded_supported_orientation (X : TopCat.{0}) [T2Space X]
    (S : Closeds X) (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    (TopCat.Sheaf.derivedClosedSupportSections X S).obj
        (DerivedCategory.Plus.Q.obj (properCycle_bounded_chain_sheaf X N)) ≅
      (TopCat.Sheaf.derivedClosedSupportSections X S).obj
        ((DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(N : ℤ))).obj
          (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))) :=
  (TopCat.Sheaf.derivedClosedSupportSections X S).mapIso
    (properCycle_bounded_derived_orientation X N c hlocal hvan)

/-- The original right-derived unit followed by the actual supported orientation compares termwise bounded chain sections with derived sections of the original shifted constant sheaf. This is a specified map, without an assertion that the unit is invertible.
Source: CategoryTheory.Functor.rightDerivedFunctorPlusUnit; properCycle_bounded_supported_orientation.
HC no distance; AV milestone no distance. -/
def properCycle_bounded_supported_section_comparison (X : TopCat.{0}) [T2Space X]
    (S : Closeds X) (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    DerivedCategory.Plus.Q.obj
        ((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
          (properCycle_bounded_chain_sheaf X N)) ⟶
      (TopCat.Sheaf.derivedClosedSupportSections X S).obj
        ((DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(N : ℤ))).obj
          (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))) :=
  (TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app
      (properCycle_bounded_chain_sheaf X N) ≫
    (properCycle_bounded_supported_orientation X S N c hlocal hvan).hom

example (X : TopCat.{0}) [T2Space X] (S : Closeds X) (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    properCycle_bounded_supported_section_comparison X S N c hlocal hvan ≫
        (properCycle_bounded_supported_orientation X S N c hlocal hvan).inv =
      (TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app
        (properCycle_bounded_chain_sheaf X N) := by
  unfold properCycle_bounded_supported_section_comparison
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end HodgeLean.Foundations.QuotientDuality
