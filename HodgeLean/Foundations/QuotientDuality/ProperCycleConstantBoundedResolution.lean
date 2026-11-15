import HodgeLean.Foundations.QuotientDuality.ProperCycleConstantAugmentationComparison

/-! # The actual original rational resolution in the bounded derived category
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_constant_resolution_derived (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _

/-- The original rational constant augmentation identifies the original degree-zero constant object with the actual fixed bounded injective resolution in the bounded-below derived category.
Source: properCycle_constant_injective_augmentation_quasiIso; DerivedCategory.Plus.singleFunctorιIso; DerivedCategory.Plus.QCompιIso.
HC no distance; AV milestone no distance. -/
def properCycle_constant_bounded_resolution_iso (X : TopCat.{0}) :
    (DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) ≅
      DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj
          (properCycle_bounded_constant_injective X)) := by
  letI := properCycle_constant_injective_augmentation_quasiIso X
  exact DerivedCategory.Plus.ι.preimageIso
    (((DerivedCategory.Plus.singleFunctorιIso _ 0).app
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))) ≪≫
      asIso (DerivedCategory.Q.map (properCycle_constant_injective_augmentation X)) ≪≫
      ((DerivedCategory.Plus.QCompιIso _).app
        ((InjectiveObject.ι (TopCat.Sheaf AddCommGrpCat.{0} X)).mapCochainComplexPlus.obj
          (properCycle_bounded_constant_injective X))).symm)

example (X : TopCat.{0}) :
    (properCycle_constant_bounded_resolution_iso X).hom ≫
      (properCycle_constant_bounded_resolution_iso X).inv = 𝟙 _ :=
  (properCycle_constant_bounded_resolution_iso X).hom_inv_id

end HodgeLean.Foundations.QuotientDuality
