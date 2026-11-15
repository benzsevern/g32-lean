import HodgeLean.Foundations.Program.G32Native.PairedC3EvaluationLinear
import HodgeLean.Foundations.Program.G32Native.PairedC3DualEvaluationFrame

/-! # Coefficients of sections evaluated on their specified dual frame -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Evaluation on the specified dual frame recovers the actual coefficient
of the section, in the original ring of sections. -/
theorem paired_c3_dual_frame_coefficient {X : Scheme.{0}} (L : X.Modules)
    (s t : Γ(L, ⊤)) (U : X.Opens) (c : Γ(X, U))
    (hs : IsFrameOn (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) U)
    (h : c • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) :
    (show Γ(X, U) from (pairedC3EvaluationAtSection L t).app U
      (pairedC3NativeDualFrameSection hs)) = c := by
  have hv := paired_c3_evaluation_at_smul L s t U c h (pairedC3NativeDualFrameSection hs)
  change (show Γ(X, U) from (pairedC3EvaluationAtSection L t).app U
    (pairedC3NativeDualFrameSection hs)) =
    c * (show Γ(X, U) from (pairedC3EvaluationAtSection L s).app U
      (pairedC3NativeDualFrameSection hs)) at hv
  rw [paired_c3_evaluation_dual_frame_self, mul_one] at hv
  exact hv

end HodgeLean.Foundations.Program.G32Native
