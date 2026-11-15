import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedSupportedOrientation

/-! # Actual bounded section homology in original derived supported cohomology
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_section_homology_derived_sheaf_category (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance properCycle_section_homology_derived_group_category :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- The specified original bounded section comparison induces the actual map from ordinary section homology into derived supported cohomology of the original shifted constant sheaf.
Source: properCycle_bounded_supported_section_comparison; DerivedCategory.homologyFunctorFactors; DerivedCategory.Plus.QCompιIso.
HC no distance; AV milestone no distance. -/
def properCycle_bounded_supported_homology_comparison (X : TopCat.{0}) [T2Space X]
    (S : Closeds X) (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) (i : ℤ) :
    (((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.up ℤ)).obj
        (properCycle_bounded_chain_sheaf X N).obj).homology i ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} i).obj
        ((TopCat.Sheaf.derivedClosedSupportSections X S).obj
          ((DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(N : ℤ))).obj
            (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)))) :=
  (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{0} i).inv.app
      (((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
        (properCycle_bounded_chain_sheaf X N)).obj) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{0} i).map
      ((DerivedCategory.Plus.QCompιIso AddCommGrpCat.{0}).inv.app
        ((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
          (properCycle_bounded_chain_sheaf X N))) ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} i).map
      (properCycle_bounded_supported_section_comparison X S N c hlocal hvan)

end HodgeLean.Foundations.QuotientDuality
