import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrameRestrictions

/-! # Frame changes for the actual native dual coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Scaling the original frame scales the evaluation coordinate by the
same function, as required for the dual line's coefficient transition. -/
theorem paired_c3_native_dual_frame_transition {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s t : Γ(M, U)} (hs : IsFrameOn s U) (ht : IsFrameOn t U)
    (c : Γ(X, U)) (hst : t = c • s) (φ : Γ(M.dual, U)) :
    pairedC3NativeDualFrameEquiv ht φ = c * pairedC3NativeDualFrameEquiv hs φ := by
  let ψ := (pairedC3DualPresheafIso M).hom.val.app (op U) φ
  change ψ.1 (𝟙 (op U)) t = c • ψ.1 (𝟙 (op U)) s
  rw [hst]
  exact (ψ.1 (𝟙 (op U))).map_smul c s

#print axioms paired_c3_native_dual_frame_transition
end HodgeLean.Foundations.Program.G32Native
