import HodgeLean.Foundations.QuotientDuality.RetainedCycleBoundedGlobalUnit
import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportForgetting

/-! # Detection of the supported derived unit by forgetting support -/

noncomputable section
open CategoryTheory TopologicalSpace
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance supportedDetectionSheafDerived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) := HasDerivedCategory.standard _
local instance supportedDetectionGroupDerived : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- A section class with nonzero global image stays nonzero under the original supported derived unit. -/
theorem retained_supported_unit_nonzero_of_global_image
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N : ℕ) (o : LocalRationalOrientation X (N+1))
    (S : Closeds X) (i : ℤ) (hi : -((N+1 : ℕ) : ℤ)+1 < i)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat i).obj
      (DerivedCategory.Plus.Q.obj ((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
        (properCycle_bounded_chain_sheaf X (N+1)))))
    (ha : ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat i).map
      (DerivedCategory.Plus.Q.map ((retainedSupportForgetting X S).mapCochainComplexPlus.app
        (properCycle_bounded_chain_sheaf X (N+1))))).hom a ≠ 0) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat i).map
      ((TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app
        (properCycle_bounded_chain_sheaf X (N+1)))).hom a ≠ 0 := by
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat i
  let K := properCycle_bounded_chain_sheaf X (N+1)
  let τ := retainedSupportForgetting X S
  have hn := NatTrans.rightDerivedFunctorPlus_fac_app τ K
  have he := ConcreteCategory.congr_hom (congrArg (fun g => H.map g) hn) a
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at he
  change (H.map (τ.rightDerivedFunctorPlus.app _)).hom
      ((H.map ((TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app K)).hom a) =
    (H.map ((subdivisionGlobalSectionsFunctor X).rightDerivedFunctorPlusUnit.app K)).hom
      ((H.map (DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app K))).hom a) at he
  intro hz
  change (H.map ((TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app K)).hom a = 0 at hz
  rw [hz, map_zero] at he
  exact ha (retained_bounded_global_unit_injective X t N o i hi
    (he.symm.trans (map_zero _).symm))

/-- Nonzero ordinary section homology images are detected in the canonical supported unit coordinates. -/
theorem retained_supported_raw_unit_nonzero_of_global_image
    (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N : ℕ) (o : LocalRationalOrientation X (N+1))
    (S : Closeds X) (i : ℤ) (hi : -((N+1 : ℕ) : ℤ)+1 < i)
    (a : (((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.up ℤ)).obj
      (properCycle_bounded_chain_sheaf X (N+1)).obj).homology i)
    (ha : (HomologicalComplex.homologyMap
      (((retainedSupportForgetting X S).mapHomologicalComplex (.up ℤ)).app
        (properCycle_bounded_chain_sheaf X (N+1)).obj) i).hom a ≠ 0) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat i).map
      ((TopCat.Sheaf.closedSupportSections X S).rightDerivedFunctorPlusUnit.app
        (properCycle_bounded_chain_sheaf X (N+1)))).hom
      (((retainedPlusHomologyComparison AddCommGrpCat i).inv.app
        ((TopCat.Sheaf.closedSupportSections X S).mapCochainComplexPlus.obj
          (properCycle_bounded_chain_sheaf X (N+1)))).hom a) ≠ 0 := by
  apply retained_supported_unit_nonzero_of_global_image X t N o S i hi
  exact retained_plus_homology_inverse_map_nonzero
    ((retainedSupportForgetting X S).mapCochainComplexPlus.app
      (properCycle_bounded_chain_sheaf X (N+1))) i a ha

end HodgeLean.Foundations.QuotientDuality
