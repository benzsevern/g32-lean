import HodgeLean.Foundations.Program.G32Native.PairedConormalIntegralRatios
import HodgeLean.Foundations.Program.G32Native.PairedConormalGradedChartEvaluation

/-! # Evaluation of normalized fractions on the actual affine chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pulling an actual normalized fraction back along its affine chart recovers
that same fraction in the chart ring. -/
theorem conormal_awayToSection_chart_evaluation (k : ℕ) (i : Fin (k + 1))
    (h : (⊤ : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (UniversalGrading k) (X i)))).Opens) ≤
      Proj.awayι (UniversalGrading k) (X i) (isHomogeneous_X (ULift ℤ) i) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading k) (X i)) :
    Proj.awayToSection (UniversalGrading k) (X i) ≫
      (Proj.awayι (UniversalGrading k) (X i) (isHomogeneous_X (ULift ℤ) i) zero_lt_one).appLE
        (Proj.basicOpen (UniversalGrading k) (X i)) ⊤ h =
      (Scheme.ΓSpecIso (CommRingCat.of
        (HomogeneousLocalization.Away (UniversalGrading k) (X i)))).inv := by
  exact conormal_graded_awayToSection_chart_evaluation (UniversalGrading k) (X i)
    (isHomogeneous_X (ULift ℤ) i) zero_lt_one h

end HodgeLean.Foundations.Program.G32Native
