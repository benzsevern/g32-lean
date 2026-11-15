import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealSections
import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrameCoefficient
import HodgeLean.Foundations.Program.G32Native.PairedC3KernelSectionExt

/-! # The specified generator in the coordinate ideal evaluation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Evaluation sends the actual negative-line frame to the specified
ideal generator, with its original homogeneous ratio and scale. -/
theorem paired_c3_coordinate_ideal_evaluation_generator (k : ℕ) (i j : Fin (k + 1)) :
    Scheme.Modules.Hom.app (X := pairedC3Proj k) (pairedC3CoordinateIdealEvaluation k j)
      (ProjSpace.standardOpen ℂ k i)
      (pairedC3CoordinateDualGenerator k i) = pairedC3CoordinateIdealStandardSection k i j := by
  exact paired_c3_kernel_lift_section (X := pairedC3Proj k)
    (SheafOfModules.unitToPushforwardObjUnit
      (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom)
    (pairedC3CoordinateEvaluation k j)
    (paired_c3_coordinate_evaluation_restriction_zero k j)
    (ProjSpace.standardOpen ℂ k i) (pairedC3CoordinateDualGenerator k i)
    (pairedC3CoordinateIdealStandardSection k i j) (by
      exact (paired_c3_dual_frame_coefficient (ProjSpace.twistingSheaf ℂ k)
        (ProjSpace.twistingCoordinateSection ℂ k i) (ProjSpace.twistingCoordinateSection ℂ k j)
        (ProjSpace.standardOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i j)
        ((ProjSpace.isFrameOn_twistingCoordinateSection ℂ k i).map
          (homOfLE (le_top : ProjSpace.standardOpen ℂ k i ≤ ⊤)))
        (ProjSpace.coordinateRatioSection_smul_twistingCoordinateSection ℂ k i j)).trans
          (paired_c3_coordinate_ideal_standard_section_inclusion k i j).symm)

end HodgeLean.Foundations.Program.G32Native
