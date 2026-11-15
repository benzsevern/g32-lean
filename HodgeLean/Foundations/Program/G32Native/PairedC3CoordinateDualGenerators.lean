import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedC3NativeDualFrames

/-! # Specified generators of the actual negative line on coordinate charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The native dual generator evaluating to one on the original coordinate frame. -/
def pairedC3CoordinateDualGenerator (k : ℕ) (i : Fin (k + 1)) :
    Γ(pairedC3NegativeLine k, ProjSpace.standardOpen ℂ k i) :=
  pairedC3NativeDualFrameSection
    ((ProjSpace.isFrameOn_twistingCoordinateSection ℂ k i).map
      (homOfLE (le_top : ProjSpace.standardOpen ℂ k i ≤ ⊤)))

/-- The specified coordinate dual generator is an actual frame. -/
theorem paired_c3_coordinate_dual_generator_frame (k : ℕ) (i : Fin (k + 1)) :
    IsFrameOn (pairedC3CoordinateDualGenerator k i) (ProjSpace.standardOpen ℂ k i) :=
  paired_c3_native_dual_frame
    ((ProjSpace.isFrameOn_twistingCoordinateSection ℂ k i).map
      (homOfLE (le_top : ProjSpace.standardOpen ℂ k i ≤ ⊤)))

#print axioms pairedC3CoordinateDualGenerator
#print axioms paired_c3_coordinate_dual_generator_frame
end HodgeLean.Foundations.Program.G32Native
