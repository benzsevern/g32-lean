import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

/-! # Original standard complex local class under actual complex linear coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Every actual continuous complex linear coordinate equivalence preserves the specified original standard complex local class through its literal point-pair map.
Source: relativeHomologyMap_complexMatrix_standardComplexLocalClass; complexMatrixOfContinuousLinearMap_det_ne_zero.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_linear_standard_orientation (d : ℕ)
    (L : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) :
    let E : puncturedPair ℂ d ≅ puncturedPair ℂ d := TopPair.isoOfSubset L.toHomeomorph (fun _ => not_congr L.map_eq_zero_iff)
    relativeHomologyMap ℚ (2*d) E.hom (standardComplexLocalClass ℚ d) =
      standardComplexLocalClass ℚ d := by
  let E : puncturedPair ℂ d ≅ puncturedPair ℂ d := TopPair.isoOfSubset L.toHomeomorph (fun _ => not_congr L.map_eq_zero_iff)
  let A := complexMatrixOfContinuousLinearMap d L.toContinuousLinearMap
  let hA := complexMatrixOfContinuousLinearMap_det_ne_zero d L.toContinuousLinearMap L.injective
  have hp : complexMatrixPuncturedPairMap d A hA = E.hom := by
    ext z : 2
    · apply Subtype.ext
      change A.mulVec z.1 = L z.1
      exact complexMatrixOfContinuousLinearMap_mulVec d L.toContinuousLinearMap z.1
    · change A.mulVec z = L z
      exact complexMatrixOfContinuousLinearMap_mulVec d L.toContinuousLinearMap z
  have h := relativeHomologyMap_complexMatrix_standardComplexLocalClass d A hA
  rw [hp] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
