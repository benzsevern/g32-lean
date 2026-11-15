import HodgeLean.Foundations.QuotientDuality.ProperCycleConstantInjectiveAugmentation

/-! # The original constant augmentation retains actual cohomology
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original integer-graded constant rational augmentation is a quasi-isomorphism, retaining the original resolution augmentation and the actual single-complex identification.
Source: CategoryTheory.InjectiveResolution.quasiIso; HomologicalComplex.quasiIso_extendMap_iff; properCycle_constant_injective_augmentation.
HC no distance; AV milestone no distance. -/
lemma properCycle_constant_injective_augmentation_quasiIso (X : TopCat.{0}) :
    QuasiIso (properCycle_constant_injective_augmentation X) := by
  letI := (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).quasiIso
  haveI : QuasiIso (HomologicalComplex.extendMap
      (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance
  unfold properCycle_constant_injective_augmentation
  exact quasiIso_comp _ _

end HodgeLean.Foundations.QuotientDuality
