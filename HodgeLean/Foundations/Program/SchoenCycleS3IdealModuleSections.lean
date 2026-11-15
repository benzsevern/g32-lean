import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Sections of the immersion ideal module -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Evaluation identifies the ideal module with the kernel of the map on sections. -/
def s2e_idealModuleSectionsIso {K B : Scheme} (f : K ⟶ B) (U : B.Opens) :
    (SheafOfModules.evaluation B.ringCatSheaf (.op U)).obj (s2c_idealModule f) ≅
      ModuleCat.of Γ(B, U) (RingHom.ker (f.app U).hom) := by
  let e := SheafOfModules.evaluation B.ringCatSheaf (.op U)
  letI : e.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  exact PreservesKernel.iso e g ≪≫ ModuleCat.kernelIsoKer (e.map g)

/-- On an affine open the module kernel is the specified subscheme ideal. -/
def s2e_subschemeIdealModuleSectionsIso {B : Scheme} (I : B.IdealSheafData)
    (U : B.affineOpens) :
    (SheafOfModules.evaluation B.ringCatSheaf (.op U.1)).obj
        (s2c_idealModule I.subschemeι) ≅ ModuleCat.of Γ(B, U.1) (I.ideal U) :=
  s2e_idealModuleSectionsIso I.subschemeι U.1 ≪≫
    (LinearEquiv.ofEq _ _ (I.ker_subschemeι_app U)).toModuleIso

end HodgeLean.Foundations.Program
