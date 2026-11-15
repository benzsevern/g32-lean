import HodgeLean.Foundations.QuotientDuality.ProperCycleUnitAugmentation

/-! # Original relative degree-zero classes under actual unit evaluation
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual relative pushforward retains cup-unit evaluation through the specified inverse relative projections when those chain projections are isomorphisms.
Source: HodgeLean.RealDefs.augmentationFunctional_relativeHomologyMap; properCycle_unit_pairing_augmentation.
HC no distance; AV milestone no distance. -/
theorem properCycle_relative_unit_pushforward
    {P Q : TopPair.{0}} [IsIso (relativeChainProjection ℚ P)]
    [IsIso (relativeChainProjection ℚ Q)] (f : P ⟶ Q) (z : RelativeHomology ℚ P 0) :
    let EP := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0
    let EQ := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ Q)) 0
    cohomologyEquivDualHomology ℚ Q.fst 0 (unit (R := ℚ) Q.fst)
      (EQ.inv.hom (relativeHomologyMap ℚ 0 f z)) =
      cohomologyEquivDualHomology ℚ P.fst 0 (unit (R := ℚ) P.fst) (EP.inv.hom z) := by
  dsimp only
  rw [properCycle_unit_pairing_augmentation, properCycle_unit_pairing_augmentation]
  exact HodgeLean.RealDefs.augmentationFunctional_relativeHomologyMap f z

/-- The specified standard complex zero-dimensional local class has original cup-unit evaluation one under the actual inverse relative projection.
Source: HodgeLean.RealDefs.augmentationFunctional_standardComplexLocalClass_zero; properCycle_unit_pairing_augmentation.
HC no distance; AV milestone no distance. -/
theorem properCycle_standard_complex_zero_unit :
    let E := HomologicalComplex.homologyMapIso
      (asIso (relativeChainProjection ℚ (puncturedPair ℂ 0))) 0
    cohomologyEquivDualHomology ℚ (TopCat.of (Fin 0 → ℂ)) 0
      (unit (R := ℚ) (TopCat.of (Fin 0 → ℂ)))
      (E.inv.hom (standardComplexLocalClassMul 0)) = 1 := by
  dsimp only
  rw [properCycle_unit_pairing_augmentation]
  exact HodgeLean.RealDefs.augmentationFunctional_standardComplexLocalClass_zero

end HodgeLean.Foundations.QuotientDuality
