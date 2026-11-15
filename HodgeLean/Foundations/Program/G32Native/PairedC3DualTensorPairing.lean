import HodgeLean.Foundations.Program.G32Native.PairedC3TensorDesc
import HodgeLean.Foundations.Program.G32Native.PairedC3NativeDualFrames
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.TensorWithFrame
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.InvertibleExactness

/-! # The actual dual tensor evaluation -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Evaluate the actual natural dual functional on the original section,
using the native sheafified tensor product. -/
def pairedC3DualTensorPairing {X : Scheme.{0}} (L : X.Modules) :
    L ⊗ L.dual ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  pairedC3TensorDesc (PresheafOfModules.uncurry' L.val (pairedC3DualPresheafIso L).hom.val)

/-- Evaluation keeps both original sections, before choosing a local frame. -/
theorem paired_c3_dual_tensor_pairing_sections {X : Scheme.{0}} (L : X.Modules)
    (U : X.Opens) (s : Γ(L, U)) (φ : Γ(L.dual, U)) :
    (pairedC3DualTensorPairing L).app U (tensorSections s φ) =
      pairedC3FrameEvaluation s ((pairedC3DualPresheafIso L).hom.val.app (op U) φ) := by
  rw [pairedC3DualTensorPairing, paired_c3_tensor_desc_sections]
  exact PresheafOfModules.uncurry'_app_tmul L.val (pairedC3DualPresheafIso L).hom.val s φ

#print axioms paired_c3_dual_tensor_pairing_sections
/-- Evaluation of the restricted original frame against its native dual
frame is one on every smaller open. -/
theorem paired_c3_dual_tensor_frame_value {X : Scheme.{0}} {L : X.Modules}
    {U : X.Opens} {s : Γ(L, U)} (hs : IsFrameOn s U)
    (W : X.Opens) (h : W ≤ U) :
    (pairedC3DualTensorPairing L).app W
      (tensorSections (L.presheaf.map (homOfLE h).op s)
        (L.dual.presheaf.map (homOfLE h).op (pairedC3NativeDualFrameSection hs))) =
      (1 : Γ(X, W)) := by
  rw [paired_c3_dual_tensor_pairing_sections]
  change pairedC3NativeDualFrameEquiv ((hs.map (homOfLE h)).mono h)
      (L.dual.presheaf.map (homOfLE h).op (pairedC3NativeDualFrameSection hs)) = 1
  rw [paired_c3_native_dual_frame_restrict]
  change X.presheaf.map (homOfLE h).op
      (pairedC3NativeDualFrameEquiv hs ((pairedC3NativeDualFrameEquiv hs).symm 1)) = 1
  rw [LinearEquiv.apply_symm_apply, map_one]

#print axioms paired_c3_dual_tensor_frame_value
end HodgeLean.Foundations.Program.G32Native
