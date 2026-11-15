import HodgeLean.Foundations.Connected
import HodgeLean.Foundations.Port.AlgebraicGeometry.Cohomology.SingularComparison
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CohomologyZero
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

/-!
# Rational sheaf-to-singular comparison for projective varieties

U1 is available as a linear equivalence. Naturality in `X` is not provided.
HC: no distance. AV milestone: no distance. Connectedness is supplied by
`pathConnectedSpace_complexPoint`, allowing the downstream adapter to retire
`ComplexPointsPreconnected`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations

/-- U1 for projective `X`, supplying the Hausdorff and hereditary-paracompactness inputs.
This is a linear equivalence; no naturality in `X` is asserted.

Source: upstream `Other/AlgebraicGeometry/Cohomology/SingularComparison.lean` at `2ead713`,
`ComplexPoint.rationalCohomologyLinearEquivSingularCohomology`. -/
noncomputable def rationalCohomologyLinearEquivSingular (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    H^n(X; ℚ) ≃ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) n := by
  letI (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  exact rationalCohomologyLinearEquivSingularCohomology X n

-- The wrapper transports degree zero to a one-dimensional space.
-- Specializing to Spec ℂ also requires a projective presentation of its identity morphism;
-- upstream's explicit-presentation IsProjective API does not supply that instance.
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Module.finrank ℚ H^0(X; ℚ) = 1 := by
  let : PathConnectedSpace (ComplexPoint X) := pathConnectedSpace_complexPoint X
  rw [(rationalCohomologyLinearEquivSingular X 0).finrank_eq]
  apply finrank_eq_one_iff'.mpr
  exact ⟨AlgebraicTopology.Singular.cohomologyUnitZero ℚ (TopCat.of (ComplexPoint X)),
    AlgebraicTopology.Singular.cohomologyUnitZero_ne_zero ℚ (TopCat.of (ComplexPoint X)),
    AlgebraicTopology.Singular.exists_smul_cohomologyUnitZero ℚ
      (TopCat.of (ComplexPoint X))⟩

-- A concrete one-point test of the singular-cohomology target.
example :
    Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of PUnit) 0) = 1 := by
  apply finrank_eq_one_iff'.mpr
  exact ⟨AlgebraicTopology.Singular.cohomologyUnitZero ℚ (TopCat.of PUnit),
    AlgebraicTopology.Singular.cohomologyUnitZero_ne_zero ℚ (TopCat.of PUnit),
    AlgebraicTopology.Singular.exists_smul_cohomologyUnitZero ℚ (TopCat.of PUnit)⟩

end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.rationalCohomologyLinearEquivSingular
