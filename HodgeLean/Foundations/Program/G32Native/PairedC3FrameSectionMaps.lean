import HodgeLean.Foundations.Curves.Picard.LineBundles.SectionMaps
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.Frames

/-! # Section morphisms from specified local frames -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules HodgeLean.Foundations.Curves.Picard.LineBundles

/-- A local frame makes its actual section morphism invertible. -/
theorem paired_c3_local_section_hom_isIso {X : Scheme.{0}} (M : X.Modules)
    (U : X.Opens) (s : Γ(M, U)) (hs : IsFrameOn s U) :
    IsIso (localSectionHom M U s) := by
  apply module_isIso_of_affine_app
  intro V
  have hb := hs (U.ι_image_le V.1) (U.ι_image_le V.1)
  have hi := ConcreteCategory.bijective_of_isIso (U.ι.appIso V.1).inv
  exact hb.comp hi

/-- A module morphism carries the original section morphism to the
section morphism of its image, with the actual restriction maps. -/
theorem paired_c3_local_section_hom_naturality {X : Scheme.{0}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    localSectionHom M U s ≫ (restrictFunctor U.ι).map f =
      localSectionHom N U (f.app U s) := by
  ext V a
  change f.app (U.ι ''ᵁ V)
    ((U.ι.appIso V).inv a • M.presheaf.map (homOfLE (U.ι_image_le V)).op s) =
    (U.ι.appIso V).inv a • N.presheaf.map (homOfLE (U.ι_image_le V)).op (f.app U s)
  rw [Scheme.Modules.Hom.app_smul]
  congr 1
  exact PresheafOfModules.naturality_apply f.val (homOfLE (U.ι_image_le V)).op s

end HodgeLean.Foundations.Program.G32Native
