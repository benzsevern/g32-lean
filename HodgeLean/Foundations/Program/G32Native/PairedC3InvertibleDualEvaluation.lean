import HodgeLean.Foundations.Program.G32Native.PairedC3DualEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedC3NativeDualFrames
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.InvertibleExactness
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- In frame coordinates, native evaluation multiplies the functional value by the coordinate. -/
theorem paired_c3_dual_evaluation_frame_expansion {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U)
    (φ : Γ(M.dual, U)) (y : Γ(M, U)) :
    (pairedC3DualEvaluation M).app U (tensorSections y φ) =
      pairedC3NativeDualFrameEquiv hs φ *
        (pairedC3FrameEquiv hs le_rfl le_rfl).symm y := by
  rw [paired_c3_dual_evaluation_tensor]
  let ψ := (pairedC3DualPresheafIso M).hom.app U φ
  have h := paired_c3_frame_functional_expansion hs ψ (𝟙 (op U)) y
  rw [X.presheaf.map_id] at h
  exact h

/-- Evaluation is bijective on every open contained in an actual frame open. -/
theorem paired_c3_dual_evaluation_bijective_below_frame {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U)
    (W : X.Opens) (hWU : W ≤ U) :
    Function.Bijective ((pairedC3DualEvaluation M).app W) := by
  let q := pairedC3NativeDualFrameSection hs
  have hq : IsFrameOn q U := paired_c3_native_dual_frame hs
  let qW : Γ(M.dual, W) := M.dual.presheaf.map (homOfLE hWU).op q
  let hsW := ((hs.map (homOfLE hWU)).mono hWU)
  have hqw : pairedC3NativeDualFrameEquiv hsW qW = 1 := by
    have h := paired_c3_native_dual_frame_restrict hs hWU q
    change pairedC3NativeDualFrameEquiv hsW qW =
      X.presheaf.map (homOfLE hWU).op
        ((pairedC3NativeDualFrameEquiv hs) ((pairedC3NativeDualFrameEquiv hs).symm 1)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.trans (map_one _)
  have hb : Function.Bijective (fun y : Γ(M, W) => tensorSections y qW) :=
    hq.bijective_tensorSections M hWU hWU
  have he : (fun y : Γ(M, W) =>
      (pairedC3DualEvaluation M).app W (tensorSections y qW)) =
      fun y => (pairedC3FrameEquiv hsW le_rfl le_rfl).symm y := by
    funext y
    rw [paired_c3_dual_evaluation_frame_expansion hsW, hqw, one_mul]
  have hc : Function.Bijective (fun y : Γ(M, W) =>
      (pairedC3DualEvaluation M).app W (tensorSections y qW)) := by
    rw [he]
    exact (pairedC3FrameEquiv hsW le_rfl le_rfl).symm.bijective
  exact (Function.Bijective.of_comp_iff _ hb).mp hc

/-- Evaluation identifies an invertible sheaf tensored with its native dual with the unit.
Source: Hartshorne, Algebraic Geometry, II.5, invertible sheaves and their duals. -/
theorem paired_c3_invertible_dual_evaluation_isIso {X : Scheme.{0}} {M : X.Modules}
    (hM : IsInvertible M) : IsIso (pairedC3DualEvaluation M) := by
  obtain ⟨U, s, hs, hcover⟩ := hM.exists_frame_cover
  apply Hom.isIso_of_isIso_app_of_iSup_eq_top (pairedC3DualEvaluation M) U hcover
  intro x W hWU
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (paired_c3_dual_evaluation_bijective_below_frame (hs x) W hWU)

/-- The actual native negative line cancels the actual positive twisting line.
Source: Hartshorne, Algebraic Geometry, II.5, invertible sheaves and their duals. -/
def pairedC3NegativePositiveIso (k : ℕ) :
    pairedC3NegativeLine k ⊗ ProjSpace.twistingSheaf ℂ k ≅
      𝟙_ (pairedC3Proj k).Modules := by
  let M : (pairedC3Proj k).Modules := ProjSpace.twistingSheaf ℂ k
  letI := paired_c3_invertible_dual_evaluation_isIso
    (ProjSpace.isInvertible_twistingSheaf ℂ k)
  exact (β_ M.dual M) ≪≫ asIso (pairedC3DualEvaluation M)

end HodgeLean.Foundations.Program.G32Native
