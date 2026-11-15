import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroAbsoluteNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleUnitAugmentation

/-! # The zero-dimensional normal coclass and the singular cup unit

Consumer: RetainedCycleConsumerSteps.lean:42, through RetainedCycleProofs.lean:249.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Forgetting the empty relative subspace carries the augmentation class to the singular cup unit. -/
lemma retained_augmentation_class_absolute_unit
    (P : TopPair.{0}) [IsIso (relativeChainProjection ℚ P)] :
    relativeCohomologyToAbsolute ℚ P 0 (HodgeLean.RealDefs.augmentationClass P) =
      unit (R := ℚ) P.fst := by
  apply (cohomologyEquivDualHomology ℚ P.fst 0).injective
  ext z
  rw [cohomologyEquivDualHomology_relativeCohomologyToAbsolute,
    HodgeLean.RealDefs.augmentationClass, LinearEquiv.apply_symm_apply,
    properCycle_unit_pairing_augmentation]
  let E := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0
  change (E.inv ≫ P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
    (E.hom.hom z) = _
  exact ConcreteCategory.congr_hom (Iso.hom_inv_id_assoc E
    (P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ))) z

/-- The original zero-dimensional normal absolute coclass is the singular cup unit on every space. -/
lemma retained_zero_normal_absolute_unit (X : TopCat.{0}) :
    properCycle_zero_normal_absolute X = unit (R := ℚ) X := by
  have h : normalizedRelativeCoclass (standardComplexLocalClass ℚ 0)
      (standardComplexLocalClass_ne_zero_for_chart 0) =
      HodgeLean.RealDefs.augmentationClass (puncturedPair ℂ 0) :=
    HodgeLean.RealDefs.normalizedPointCoclass_zero
  unfold properCycle_zero_normal_absolute
  rw [h, retained_augmentation_class_absolute_unit (puncturedPair ℂ 0)]
  change cohomologyMap ℚ 0 (TopCat.ofHom ⟨fun _ : X => (0 : Fin 0 → ℂ), continuous_const⟩)
    (unit (R := ℚ) (TopCat.of (Fin 0 → ℂ))) = unit (R := ℚ) X
  exact cohomologyMap_unit (R := ℚ) _ _

end HodgeLean.Foundations.QuotientDuality
