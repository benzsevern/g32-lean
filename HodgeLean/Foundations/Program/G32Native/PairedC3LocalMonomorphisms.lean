import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Sections.SectionsGluing

/-! # Detecting module monomorphisms on open neighbourhoods -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- A monomorphic pullback to an open detects injectivity on every smaller open. -/
theorem paired_c3_injective_app_of_mono_open_pullback
    {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (hf : Mono ((Scheme.Modules.pullback U.ι).map f))
    (V : X.Opens) (hV : V ≤ U) : Function.Injective (f.app V) := by
  let e := restrictFunctorIsoPullback U.ι
  have hm : Mono ((restrictFunctor U.ι).map f) := by
    haveI : Mono ((restrictFunctor U.ι).map f ≫ e.hom.app N) := by
      rw [e.hom.naturality f]
      letI := hf
      infer_instance
    exact mono_of_mono _ (e.hom.app N)
  have hi := (Scheme.Modules.Hom.mono_iff_injective ((restrictFunctor U.ι).map f)).mp hm
    (U.ι ⁻¹ᵁ V)
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
  change Function.Injective (f.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) at hi
  rwa [he] at hi

/-- Monomorphisms of the actual open pullbacks detect a monomorphism globally.
The proof uses separatedness on intersections with the original test open. -/
theorem paired_c3_mono_of_local_pullback
    {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.pullback U.ι).map f)) : Mono f := by
  choose U hx hU using h
  have hcover : (⨆ x, U x) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply (Scheme.Modules.Hom.mono_iff_injective f).mpr
  intro V s t hst
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (fun x => V ⊓ U x) V (fun _ => inf_le_left)
      (by rw [← inf_iSup_eq, hcover, inf_top_eq])).1
  intro x
  apply paired_c3_injective_app_of_mono_open_pullback f (U x) (hU x)
    (V ⊓ U x) inf_le_right
  have hs := PresheafOfModules.naturality_apply f.val
    (homOfLE (show V ⊓ U x ≤ V from inf_le_left)).op s
  have ht := PresheafOfModules.naturality_apply f.val
    (homOfLE (show V ⊓ U x ≤ V from inf_le_left)).op t
  change f.app (V ⊓ U x) (M.presheaf.map (homOfLE inf_le_left).op s) =
    N.presheaf.map (homOfLE inf_le_left).op (f.app V s) at hs
  change f.app (V ⊓ U x) (M.presheaf.map (homOfLE inf_le_left).op t) =
    N.presheaf.map (homOfLE inf_le_left).op (f.app V t) at ht
  exact hs.trans ((congrArg (fun z => N.presheaf.map (homOfLE inf_le_left).op z) hst).trans ht.symm)

end HodgeLean.Foundations.Program.G32Native
