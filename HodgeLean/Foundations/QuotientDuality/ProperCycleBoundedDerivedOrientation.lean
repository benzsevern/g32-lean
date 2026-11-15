import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedChainComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedOrientation
import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # The original ambient orientation in the actual bounded-below category
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_bounded_derived_category (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _

/-- The specified original ambient class orients the actual bounded chain sheaf object in the bounded-below derived category; the comparison retains the original truncation projection and derived orientation.
Source: properCycle_bounded_chain_sheaf_quasiIso; properCycle_global_derived_orientation; DerivedCategory.Plus.QCompιIso; DerivedCategory.Plus.singleFunctorιIso.
HC no distance; AV milestone no distance. -/
def properCycle_bounded_derived_orientation (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (c : Homology ℚ X N)
    (hlocal : ∀ x : X, Function.Bijective (orientationLine X N c x))
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    DerivedCategory.Plus.Q.obj (properCycle_bounded_chain_sheaf X N) ≅
      (DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(N : ℤ))).obj
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) := by
  letI := properCycle_bounded_chain_sheaf_quasiIso X N hvan
  exact DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.QCompιIso _).app (properCycle_bounded_chain_sheaf X N) ≪≫
      (asIso (DerivedCategory.Q.map
        ((singularChainSheafCochainComplex ℚ X).πTruncGE (-(N : ℤ))))).symm ≪≫
      properCycle_global_derived_orientation X N c hlocal hvan ≪≫
      ((DerivedCategory.Plus.singleFunctorιIso _ (-(N : ℤ))).app
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))).symm)

end HodgeLean.Foundations.QuotientDuality
