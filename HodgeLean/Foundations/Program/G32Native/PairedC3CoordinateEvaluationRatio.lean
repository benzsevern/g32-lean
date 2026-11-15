import HodgeLean.Foundations.Program.G32Native.PairedC3EvaluationLinear

/-! # The original homogeneous ratio in native negative-line evaluation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- In each original coordinate frame, evaluation is scalar multiplication
by its actual homogeneous ratio, with its original coordinate scale. -/
theorem paired_c3_coordinate_evaluation_ratio (k : ℕ) (i j : Fin (k + 1))
    (φ : Γ(pairedC3NegativeLine k, ProjSpace.standardOpen ℂ k i)) :
    (pairedC3CoordinateEvaluation k j).app (ProjSpace.standardOpen ℂ k i) φ =
      ProjSpace.coordinateRatioSection ℂ k i j •
        (pairedC3CoordinateEvaluation k i).app (ProjSpace.standardOpen ℂ k i) φ := by
  exact paired_c3_evaluation_at_smul (X := pairedC3Proj k) (ProjSpace.twistingSheaf ℂ k)
    (ProjSpace.twistingCoordinateSection ℂ k i) (ProjSpace.twistingCoordinateSection ℂ k j)
    (ProjSpace.standardOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i j)
    (ProjSpace.coordinateRatioSection_smul_twistingCoordinateSection ℂ k i j) φ

#print axioms paired_c3_coordinate_evaluation_ratio
end HodgeLean.Foundations.Program.G32Native
