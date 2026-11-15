import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrame

/-! # Restriction compatibility of actual dual frame evaluation -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Local functional evaluation commutes with simultaneous restriction
of the functional and the original frame section. -/
theorem paired_c3_dual_evaluation_restrict {X : Scheme.{0}} {M : X.Modules}
    {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U))
    (φ : Γ(pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf), U)) :
    pairedC3FrameEvaluation (M.presheaf.map (homOfLE h).op s)
        ((pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf)).presheaf.map
          (homOfLE h).op φ) =
      X.presheaf.map (homOfLE h).op (pairedC3FrameEvaluation s φ) := by
  have hn := φ.2 (𝟙 (op U)) (homOfLE h).op s
  change φ.1 ((homOfLE h).op ≫ 𝟙 (op V))
      (M.presheaf.map (homOfLE h).op s) = _
  rw [Category.comp_id]
  change X.presheaf.map (homOfLE h).op (φ.1 (𝟙 (op U)) s) =
    φ.1 (𝟙 (op U) ≫ (homOfLE h).op) (M.presheaf.map (homOfLE h).op s) at hn
  rw [Category.id_comp] at hn
  exact hn.symm

#print axioms paired_c3_dual_evaluation_restrict
/-- Native dual coordinates commute with the original sheaf restrictions. -/
theorem paired_c3_native_dual_frame_restrict {X : Scheme.{0}} {M : X.Modules}
    {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) (h : V ≤ U)
    (φ : Γ(M.dual, U)) :
    pairedC3NativeDualFrameEquiv ((hs.map (homOfLE h)).mono h)
        (M.dual.presheaf.map (homOfLE h).op φ) =
      X.presheaf.map (homOfLE h).op (pairedC3NativeDualFrameEquiv hs φ) := by
  change pairedC3FrameEvaluation (M.presheaf.map (homOfLE h).op s)
      ((pairedC3DualPresheafIso M).hom.val.app (op V)
        (M.dual.presheaf.map (homOfLE h).op φ)) =
    X.presheaf.map (homOfLE h).op
      (pairedC3FrameEvaluation s ((pairedC3DualPresheafIso M).hom.val.app (op U) φ))
  have hn := PresheafOfModules.naturality_apply
    (pairedC3DualPresheafIso M).hom.val (homOfLE h).op φ
  exact (congrArg (pairedC3FrameEvaluation (M.presheaf.map (homOfLE h).op s)) hn).trans
    (paired_c3_dual_evaluation_restrict h s _)

#print axioms paired_c3_native_dual_frame_restrict
end HodgeLean.Foundations.Program.G32Native
