import HodgeLean.Foundations.Program.G32Native.PairedC3FrameCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3RankOneEndomorphism
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Sections.SectionsGluing

/-! # Global scalar coefficients of an endomorphism on a specified line frame cover -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The underlying section function of a native linear component is the original section map. -/
theorem paired_c3_hom_app_linear_apply {X : Scheme.{0}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (z : Γ(M, U)) :
    (f.val.app (op U)).hom z = f.app U z := rfl

/-- The specified frame equivalence carries one to the original restricted section. -/
theorem paired_c3_frame_equiv_one {X : Scheme.{0}} {M : X.Modules}
    {U W : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) (h : W ≤ U) :
    pairedC3FrameEquiv hs h h 1 = M.presheaf.map (homOfLE h).op s := by
  change (1 : Γ(X, W)) • M.presheaf.map (homOfLE h).op s = _
  exact one_smul _ _

/-- The coefficient of the actual endomorphism in a specified local frame. -/
def pairedC3FrameEndCoefficient {X : Scheme.{0}} {M : X.Modules}
    (f : M ⟶ M) {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) : Γ(X, U) :=
  (pairedC3FrameEquiv hs le_rfl le_rfl).symm (f.app U s)

/-- Restriction retains the actual endomorphism's coefficient. -/
theorem paired_c3_frame_end_coefficient_restrict {X : Scheme.{0}} {M : X.Modules}
    (f : M ⟶ M) {U W : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) (h : W ≤ U) :
    X.presheaf.map (homOfLE h).op (pairedC3FrameEndCoefficient f hs) =
      (pairedC3FrameEquiv hs h h).symm (f.app W (M.presheaf.map (homOfLE h).op s)) := by
  have hc := paired_c3_frame_coordinate_restrict hs le_rfl le_rfl h (f.app U s)
  have hn := PresheafOfModules.naturality_apply f.val (homOfLE h).op s
  change f.app W (M.presheaf.map (homOfLE h).op s) =
    M.presheaf.map (homOfLE h).op (f.app U s) at hn
  rw [← hn] at hc
  exact hc.symm

/-- The coefficients in two actual frames agree on their overlap. -/
theorem paired_c3_frame_end_coefficient_overlap {X : Scheme.{0}} {M : X.Modules}
    (f : M ⟶ M) {U V : X.Opens} {s : Γ(M, U)} {t : Γ(M, V)}
    (hs : IsFrameOn s U) (ht : IsFrameOn t V) :
    X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (pairedC3FrameEndCoefficient f hs) =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (pairedC3FrameEndCoefficient f ht) := by
  rw [paired_c3_frame_end_coefficient_restrict, paired_c3_frame_end_coefficient_restrict]
  have hh := paired_c3_rank_one_end_coefficient_independent
    (pairedC3FrameEquiv hs inf_le_left inf_le_left)
    (pairedC3FrameEquiv ht inf_le_right inf_le_right)
    (f.val.app (op (U ⊓ V))).hom
  simp only [paired_c3_frame_equiv_one] at hh
  exact (congrArg (pairedC3FrameEquiv hs inf_le_left inf_le_left).symm
    (paired_c3_hom_app_linear_apply f (U ⊓ V)
      (M.presheaf.map (homOfLE inf_le_left).op s))).symm.trans
    (hh.trans (congrArg (pairedC3FrameEquiv ht inf_le_right inf_le_right).symm
      (paired_c3_hom_app_linear_apply f (U ⊓ V)
        (M.presheaf.map (homOfLE inf_le_right).op t))))

/-- Actual line-frame coefficients glue to a global structure section,
and multiplication by that same section gives the original endomorphism. -/
theorem paired_c3_end_coefficient_global {X : Scheme.{0}} {M : X.Modules}
    (f : M ⟶ M) {ι : Type} (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤)
    (s : ∀ i, Γ(M, U i)) (hs : ∀ i, IsFrameOn (s i) (U i)) :
    ∃ c : Γ(X, ⊤), ∀ (W : X.Opens) (z : Γ(M, W)),
      f.app W z = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op c • z := by
  let O := SheafOfModules.unit X.ringCatSheaf
  obtain ⟨c, hc⟩ := (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible O U ⊤
    (fun _ => le_top) hU.ge).2 (fun i => pairedC3FrameEndCoefficient f (hs i))
      (fun i j => paired_c3_frame_end_coefficient_overlap f (hs i) (hs j))
  refine ⟨c, ?_⟩
  intro W z
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (fun i => W ⊓ U i) W (fun _ => inf_le_left)
      (by rw [← inf_iSup_eq, hU, inf_top_eq])).1
  intro i
  let V := W ⊓ U i
  let E := pairedC3FrameEquiv (hs i) (show V ≤ U i from inf_le_right) inf_le_right
  let zV := M.presheaf.map (homOfLE (show V ≤ W from inf_le_left)).op z
  have hci : X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op c =
      pairedC3FrameEndCoefficient f (hs i) := hc i
  have hcoef : E.symm ((f.val.app (op V)).hom (E 1)) =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c := by
    rw [paired_c3_hom_app_linear_apply, paired_c3_frame_equiv_one]
    dsimp only [E]
    rw [← paired_c3_frame_end_coefficient_restrict, ← hci]
    rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
    rfl
  have hval := paired_c3_rank_one_end_apply E (f.val.app (op V)).hom zV
  have hval' : f.app V zV =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c • zV :=
    hval.trans (congrArg (fun a : Γ(X, V) => a • zV) hcoef)
  have hn := PresheafOfModules.naturality_apply f.val
    (homOfLE (show V ≤ W from inf_le_left)).op z
  change f.app V zV = M.presheaf.map (homOfLE inf_le_left).op (f.app W z) at hn
  rw [← hn, hval', M.map_smul]
  congr 1
  rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
  rfl

end HodgeLean.Foundations.Program.G32Native
