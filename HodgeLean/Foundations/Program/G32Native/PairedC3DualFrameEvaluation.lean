import HodgeLean.Foundations.Program.G32Native.PairedC3DualEvaluationFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3EvaluationLinear
import HodgeLean.Foundations.Program.G32Native.PairedC3NativeDualFrames

/-! # Evaluation on dual frames before specializing the ambient scheme -/
noncomputable section
set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- A specified scalar relation is the actual value on the specified dual
frame. The equality takes place in the original structure-module sections. -/
theorem paired_c3_dual_frame_evaluation_of_smul {X : Scheme.{0}} (L : X.Modules)
    (s t : Γ(L, ⊤)) (U : X.Opens) (c : Γ(X, U))
    (hs : IsFrameOn (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) U)
    (h : c • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) :
    (pairedC3EvaluationAtSection L t).app U (pairedC3NativeDualFrameSection hs) = c := by
  let toRing : Γ(SheafOfModules.unit X.ringCatSheaf, U) → Γ(X, U) := fun z => z
  apply (show Function.Injective toRing from fun _ _ h => h)
  have he : toRing ((pairedC3EvaluationAtSection L s).app U
      (pairedC3NativeDualFrameSection hs)) = 1 :=
    paired_c3_evaluation_dual_frame_self L s U hs
  have hr := congrArg toRing (paired_c3_evaluation_at_smul L s t U c h
    (pairedC3NativeDualFrameSection hs))
  change toRing ((pairedC3EvaluationAtSection L t).app U
      (pairedC3NativeDualFrameSection hs)) =
    c * toRing ((pairedC3EvaluationAtSection L s).app U
      (pairedC3NativeDualFrameSection hs)) at hr
  exact hr.trans (by rw [he, mul_one])

#print axioms paired_c3_dual_frame_evaluation_of_smul
end HodgeLean.Foundations.Program.G32Native
