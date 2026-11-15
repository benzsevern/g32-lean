import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Actual local sections of a structure-module quotient -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- An actual section on a scheme open supplies the compatible section
family of the original module on the corresponding slice site. -/
def paired_module_overSection {X : Scheme} (M : X.Modules) (U : X.Opens)
    (z : Γ(M, U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk (fun W => M.val.map W.unop.hom.op z) (by
    intro V W h
    change M.val.map h.unop.left.op (M.val.map V.unop.hom.op z) =
      M.val.map W.unop.hom.op z
    rw [← M.val.map_comp_apply]
    apply M.val.congr_map_apply
    exact congrArg Quiver.Hom.op (Over.w h.unop))

/-- A lift of the actual unit on an open constructs a section of the
original quotient on that same slice site. -/
theorem paired_unit_split_on_open_of_lift {X : Scheme} {M : X.Modules}
    (g : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (z : Γ(M, U)) (hz : g.app U z = (1 : Γ(X, U))) :
    ∃ s : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U,
      s ≫ g.over U = 𝟙 _ := by
  let N := M.over U
  let B := SheafOfModules.unit (X.ringCatSheaf.over U)
  let s := N.unitHomEquiv.symm (paired_module_overSection M U z)
  refine ⟨s, ?_⟩
  apply B.unitHomEquiv.injective
  change B.unitHomEquiv
    (N.unitHomEquiv.symm (paired_module_overSection M U z) ≫ g.over U) = _
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro W
  change g.val.app (op W.unop.left) (M.val.map W.unop.hom.op z) =
    (1 : Γ(X, W.unop.left))
  rw [PresheafOfModules.naturality_apply]
  change (X.presheaf.map W.unop.hom.op).hom (g.app U z) = (1 : Γ(X, W.unop.left))
  rw [hz, map_one]

/-- Every point has an actual open on which an epimorphism to the
structure module has a section. -/
theorem paired_unit_quotient_localSplit {X : Scheme} {M : X.Modules}
    (g : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Epi g] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ s :
      SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U,
        s ≫ g.over U = 𝟙 _ := by
  obtain ⟨U, hU, hx, z, hz⟩ := (Scheme.Modules.Hom.epi_iff_locallySurjective g).mp
    inferInstance ⊤ (1 : Γ(X, ⊤)) x (show x ∈ (⊤ : X.Opens) from trivial)
  have hz' : g.app U z = (1 : Γ(X, U)) := by
    change g.app U z = (X.presheaf.map (homOfLE hU).op).hom (1 : Γ(X, ⊤)) at hz
    simpa only [map_one] using hz
  obtain ⟨s, hs⟩ := paired_unit_split_on_open_of_lift g U z hz'
  exact ⟨U, hx, s, hs⟩

end HodgeLean.Foundations.Program.G32Native
