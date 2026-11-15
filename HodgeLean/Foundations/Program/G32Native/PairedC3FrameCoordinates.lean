import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.Frames

/-! # Scalar coordinates of an actual local module frame -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Frame coordinates are linear over the full local ring of sections. -/
def pairedC3FrameEquiv {X : Scheme.{0}} {M : X.Modules}
    {U V W : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) : Γ(X, W) ≃ₗ[Γ(X, W)] Γ(M, W) :=
  LinearEquiv.ofBijective
    { toFun := fun a => a • M.presheaf.map (homOfLE hWU).op s
      map_add' := fun _ _ => add_smul _ _ _
      map_smul' := fun _ _ => mul_smul _ _ _ }
    (hs hWU hWV)

/-- Restricting an actual section restricts its frame coefficient. -/
theorem paired_c3_frame_coordinate_restrict {X : Scheme.{0}} {M : X.Modules}
    {U V W W' : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) (h : W' ≤ W) (x : Γ(M, W)) :
    (pairedC3FrameEquiv hs (h.trans hWU) (h.trans hWV)).symm
        (M.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE h).op ((pairedC3FrameEquiv hs hWU hWV).symm x) := by
  apply (pairedC3FrameEquiv hs (h.trans hWU) (h.trans hWV)).injective
  rw [LinearEquiv.apply_symm_apply]
  have hx := (pairedC3FrameEquiv hs hWU hWV).apply_symm_apply x
  apply (congrArg (M.presheaf.map (homOfLE h).op) hx).symm.trans
  change M.presheaf.map (homOfLE h).op
      (((pairedC3FrameEquiv hs hWU hWV).symm x) •
        M.presheaf.map (homOfLE hWU).op s) = _
  rw [M.map_smul]
  congr 1
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

#print axioms pairedC3FrameEquiv
#print axioms paired_c3_frame_coordinate_restrict
end HodgeLean.Foundations.Program.G32Native
