import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeUnitAugmentation

/-! # Detection by the original relative degree-zero unit functional
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original unit functional through the actual inverse relative projection detects classes whenever the singular augmentation is an isomorphism.
Source: properCycle_unit_pairing_augmentation; Mathlib, AlgebraicTopology/SingularHomology/HomologyZero.lean.
HC no distance; AV milestone no distance. -/
theorem properCycle_relative_unit_injective
    (P : TopPair.{0}) [IsIso (relativeChainProjection ℚ P)]
    [IsIso (P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ))] :
    let E := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0
    Function.Injective (fun z : RelativeHomology ℚ P 0 =>
      cohomologyEquivDualHomology ℚ P.fst 0 (unit (R := ℚ) P.fst) (E.inv.hom z)) := by
  let E := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0
  dsimp only
  rw [properCycle_unit_pairing_augmentation]
  exact (ConcreteCategory.bijective_of_isIso
    (E.inv ≫ P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ))).1

end HodgeLean.Foundations.QuotientDuality
