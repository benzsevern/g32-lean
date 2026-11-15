import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedConstantInjective

/-! # The original constant rational augmentation in integer cochain degrees
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal augmentation of the original constant rational injective resolution, extended to integer degrees through the canonical single-complex identification.
Source: TopCat.Sheaf.ambientConstantInjectiveResolution; HomologicalComplex.extendSingleIso; HomologicalComplex.extendMap.
HC no distance; AV milestone no distance. -/
def properCycle_constant_injective_augmentation (X : TopCat.{0}) :
    (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) ⟶
      rationalConstantInjectiveComplex X :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) 0 0 rfl).inv ≫
    HomologicalComplex.extendMap
      (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι
      ComplexShape.embeddingUpNat

example (X : TopCat.{0}) :
    (properCycle_constant_injective_augmentation X).f 0 =
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) 0 0 rfl).inv ≫
        HomologicalComplex.extendMap
          (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι
          ComplexShape.embeddingUpNat).f 0 := rfl

end HodgeLean.Foundations.QuotientDuality
