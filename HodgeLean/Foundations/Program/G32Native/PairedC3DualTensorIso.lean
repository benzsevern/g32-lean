import HodgeLean.Foundations.Program.G32Native.PairedC3DualTensorPairing

/-! # Dual tensor cancellation on the actual frame cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The original evaluation map is bijective on all sections subordinate
to a frame of the original line. -/
theorem paired_c3_dual_tensor_frame_bijective {X : Scheme.{0}} {L : X.Modules}
    {U : X.Opens} {s : Γ(L, U)} (hs : IsFrameOn s U)
    (W : X.Opens) (h : W ≤ U) :
    Function.Bijective ((pairedC3DualTensorPairing L).app W) := by
  let q := L.dual.presheaf.map (homOfLE h).op (pairedC3NativeDualFrameSection hs)
  let e := pairedC3FrameEquiv hs h h
  have ht : Function.Bijective (fun m : Γ(L, W) => tensorSections m q) :=
    (paired_c3_native_dual_frame hs).bijective_tensorSections L h h
  have he : Function.Bijective (fun r : Γ(X, W) => tensorSections (e r) q) :=
    ht.comp e.bijective
  have hc (r : Γ(X, W)) :
      (pairedC3DualTensorPairing L).app W (tensorSections (e r) q) = r := by
    change (pairedC3DualTensorPairing L).app W
      (tensorSections (r • L.presheaf.map (homOfLE h).op s) q) = r
    rw [tensorSections_smul_left, Hom.app_smul]
    change r • (pairedC3DualTensorPairing L).app W
      (tensorSections (L.presheaf.map (homOfLE h).op s)
        (L.dual.presheaf.map (homOfLE h).op (pairedC3NativeDualFrameSection hs))) = r
    rw [paired_c3_dual_tensor_frame_value hs W h]
    exact mul_one r
  refine ⟨?_, fun r => ⟨tensorSections (e r) q, hc r⟩⟩
  intro a b hab
  obtain ⟨ra, rfl⟩ := he.surjective a
  obtain ⟨rb, rfl⟩ := he.surjective b
  have hr : ra = rb := (hc ra).symm.trans (hab.trans (hc rb))
  rw [hr]

#print axioms paired_c3_dual_tensor_frame_bijective
/-- Actual dual evaluation is invertible for every invertible native line.
Source: Hartshorne, Algebraic Geometry, II.5, duals of invertible sheaves. -/
theorem paired_c3_dual_tensor_pairing_isIso {X : Scheme.{0}} {L : X.Modules}
    (hL : IsInvertible L) : IsIso (pairedC3DualTensorPairing L) := by
  obtain ⟨U, s, hs, hcover⟩ := hL.exists_frame_cover
  apply Hom.isIso_of_isIso_app_of_iSup_eq_top (pairedC3DualTensorPairing L) U hcover
  intro i W hW
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (paired_c3_dual_tensor_frame_bijective (hs i) W hW)

/-- The cancellation isomorphism is the actual native dual evaluation. -/
def pairedC3DualTensorIso {X : Scheme.{0}} {L : X.Modules} (hL : IsInvertible L) :
    L ⊗ L.dual ≅ (𝟙_ X.Modules) := by
  letI := paired_c3_dual_tensor_pairing_isIso hL
  exact asIso (pairedC3DualTensorPairing L)

#print axioms paired_c3_dual_tensor_pairing_isIso
#print axioms pairedC3DualTensorIso
end HodgeLean.Foundations.Program.G32Native
