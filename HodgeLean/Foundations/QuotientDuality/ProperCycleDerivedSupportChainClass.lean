import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedSupportChainMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedSupportedHomology

/-! # Original finite support homology classes in actual derived supported sections
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_chain_class_derived_sheaf_category (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
local instance properCycle_chain_class_derived_group_category :
    HasDerivedCategory AddCommGrpCat.{0} := HasDerivedCategory.standard _

/-- Actual rational singular homology classes of the literal support map to the original derived supported sections of the shifted constant sheaf, using the original finite-chain section map, the literal bounded projection, the right-derived unit and the specified original ambient orientation.
Source: properCycle_bounded_support_chain_map; properCycle_bounded_supported_homology_comparison; HomologicalComplex.extendHomologyIso; ShortComplex.mapHomologyIso.
HC no distance; AV milestone no distance. -/
def properCycle_derived_support_chain_class_map (X : TopCat.{0}) [T2Space X]
    (S : Closeds X) (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
        (Homology ℚ (TopCat.of (S : Set X)) n) ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (-(n : ℤ))).obj
        ((TopCat.Sheaf.derivedClosedSupportSections X S).obj
          ((DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(N : ℤ))).obj
            (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)))) :=
  (((SingularChainComplex ℚ (TopCat.of (S : Set X))).sc n).mapHomologyIso
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})).inv ≫
    ((((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).obj
      (SingularChainComplex ℚ (TopCat.of (S : Set X)))).extendHomologyIso
        ComplexShape.embeddingDownNat (by rfl)).inv ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℤ) (-(n : ℤ))).map
      (properCycle_bounded_support_chain_map X S N) ≫
    properCycle_bounded_supported_homology_comparison X S N c hlocal hvan (-(n : ℤ))

end HodgeLean.Foundations.QuotientDuality
