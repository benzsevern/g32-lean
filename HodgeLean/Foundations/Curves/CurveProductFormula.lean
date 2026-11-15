import HodgeLean.Foundations.Curves.CurveProductFormulaProofs

/-! # The product formula on curves (FROZEN SPEC, lane J1b)

The statement below passed statement review as part of the J1 spec and moved here unchanged, so
that J1 could land without it. It is an implication from the displayed curve instances only.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
  [IsLocallyNoetherian X.left] [CompactSpace X.left]

/-- The product formula: a principal divisor on a complete smooth curve has degree zero.
Source: Hartshorne, *Algebraic Geometry*, II.6, Corollary 6.10. -/
theorem degree_principalDivisor (f : X.left.functionField) (hf : f ≠ 0) :
    divisorDegree X (principalDivisor X.left f) = 0 := degree_principalDivisor_aux f hf

example (f : X.left.functionField) (hf : f ≠ 0) :
    divisorDegree X (principalDivisor X.left f) = 0 := degree_principalDivisor f hf

end HodgeLean.Foundations.Curves
