import HodgeLean.Foundations.Program.G32Native.PairedC3FrameCoordinates
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Sections.SectionsGluing

/-! # Detecting actual module maps on specified local frame generators -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- A module map vanishing on the specified generators of a frame cover
vanishes globally, with the original restriction maps retained. -/
theorem paired_c3_hom_zero_of_frame_cover {X : Scheme.{0}} {M N : X.Modules}
    {ι : Type} (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤)
    (s : ∀ i, Γ(M, U i)) (hs : ∀ i, IsFrameOn (s i) (U i))
    (φ : M ⟶ N) (hz : ∀ i, φ.app (U i) (s i) = 0) : φ = 0 := by
  ext V z
  change φ.app V z = 0
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible N
    (fun i => V ⊓ U i) V (fun _ => inf_le_left)
      (by rw [← inf_iSup_eq, hU, inf_top_eq])).1
  intro i
  rw [map_zero]
  let W := V ⊓ U i
  have hn := PresheafOfModules.naturality_apply φ.val
    (homOfLE (show W ≤ V from inf_le_left)).op z
  change φ.app W (M.presheaf.map (homOfLE inf_le_left).op z) =
    N.presheaf.map (homOfLE inf_le_left).op (φ.app V z) at hn
  rw [← hn]
  obtain ⟨c, hc⟩ := (hs i inf_le_right inf_le_right).surjective
    (M.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op z)
  have hi := PresheafOfModules.naturality_apply φ.val
    (homOfLE (show W ≤ U i from inf_le_right)).op (s i)
  change φ.app W (M.presheaf.map (homOfLE inf_le_right).op (s i)) =
    N.presheaf.map (homOfLE inf_le_right).op (φ.app (U i) (s i)) at hi
  rw [hz i, map_zero] at hi
  rw [← hc]
  change (φ.val.app (op W)) (c • _) = 0
  rw [(φ.val.app (op W)).hom.map_smul]
  exact (congrArg (fun t : Γ(N, W) => c • t) hi).trans (smul_zero c)

#print axioms paired_c3_hom_zero_of_frame_cover
end HodgeLean.Foundations.Program.G32Native
