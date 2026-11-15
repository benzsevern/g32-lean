import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrameEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateDualGenerators

/-! # Original homogeneous ratios in the actual negative-line generators -/
noncomputable section
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified dual generator evaluates to the original coordinate
ratio, retaining its normalization on every chart. -/
theorem paired_c3_coordinate_dual_generator_evaluation (k : ℕ) (i j : Fin (k + 1)) :
    (pairedC3CoordinateEvaluation k j).app (ProjSpace.standardOpen ℂ k i)
      (pairedC3CoordinateDualGenerator k i) = ProjSpace.coordinateRatioSection ℂ k i j := by
  exact paired_c3_dual_frame_evaluation_of_smul (X := pairedC3Proj k)
      (ProjSpace.twistingSheaf ℂ k)
      (ProjSpace.twistingCoordinateSection ℂ k i)
      (ProjSpace.twistingCoordinateSection ℂ k j)
      (ProjSpace.standardOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i j)
      ((ProjSpace.isFrameOn_twistingCoordinateSection ℂ k i).map
        (homOfLE (le_top : ProjSpace.standardOpen ℂ k i ≤ ⊤)))
      (ProjSpace.coordinateRatioSection_smul_twistingCoordinateSection ℂ k i j)

#print axioms paired_c3_coordinate_dual_generator_evaluation
end HodgeLean.Foundations.Program.G32Native
