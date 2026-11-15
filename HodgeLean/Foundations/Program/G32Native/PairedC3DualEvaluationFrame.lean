import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedC3NativeDualFrames

/-! # Evaluation on a specified actual native dual frame -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Evaluation on the specified dual frame retains its defining value one. -/
theorem paired_c3_evaluation_dual_frame_self {X : Scheme.{0}} (L : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens)
    (hs : IsFrameOn (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) U) :
    (show Γ(X, U) from (pairedC3EvaluationAtSection L s).app U
      (pairedC3NativeDualFrameSection hs)) = 1 := by
  change pairedC3NativeDualFrameEquiv hs ((pairedC3NativeDualFrameEquiv hs).symm 1) = 1
  exact (pairedC3NativeDualFrameEquiv hs).apply_symm_apply 1

#print axioms paired_c3_evaluation_dual_frame_self
end HodgeLean.Foundations.Program.G32Native
