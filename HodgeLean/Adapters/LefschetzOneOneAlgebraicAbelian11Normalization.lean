import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11NormalizationProofs
import HodgeLean.Foundations.Curves.CubicGroup

/-! # Unit normalization of the fixed singular comparison

The degree-zero unit fixes the scalar in every degree. HC no distance;
AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

/-- The singular constant unit is sent to the actual sheaf constant class one.
Source: Bredon, Sheaf Theory, second edition, III.1, augmentation by constant cochains;
CycleClassFlatComparisonProofs, the degree-zero constant-unit chain comparison. -/
theorem bh11_singular_unit
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    singularToFieldCohomology ℚ X 0 (Singular.unit (TopCat.of (ComplexPoint X))) =
      fieldCohomologyClass ℚ X 1 :=
  bh11_singular_unit_aux X

/-- The fixed cup comparison has scalar one in every degree.
Source: `exists_cupComparison_eq_smul`, `cupComparison_unit`, and the constant-unit comparison. -/
theorem bh11_cupComparison_eq_raw
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (v : HQ X n) :
    cupComparison X n v =
      rationalCohomologyLinearEquivSingular X n (HQ.linearEquiv X n v) :=
  bh11_cupComparison_eq_raw_aux X n v

open HodgeLean.Foundations.Curves
example := bh11_singular_unit E
example := bh11_cupComparison_eq_raw E 0 (cupUnit E)
end HodgeLean.Adapters
