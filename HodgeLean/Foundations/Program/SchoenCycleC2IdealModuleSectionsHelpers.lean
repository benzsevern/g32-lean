import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- Sections of the actual kernel-defined ideal module are the kernel of
the structure-sheaf map on that scheme open. -/
def s2e_idealModule_sections_equiv
    {K B : Scheme.{0}} (k : K ⟶ B) (U : B.Opens) :
    Γ(s2c_idealModule k, U) ≃ₗ[Γ(B, U)] RingHom.ker (k.app U).hom := by
  let α := SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  let F := SheafOfModules.evaluation B.ringCatSheaf (op U)
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (PreservesKernel.iso F α ≪≫ ModuleCat.kernelIsoKer (F.map α)).toLinearEquiv

/-- The section identification respects the actual inclusion in the
ambient structure sheaf. -/
theorem s2e_idealModule_sections_equiv_coe
    {K B : Scheme.{0}} (k : K ⟶ B) (U : B.Opens)
    (x : Γ(s2c_idealModule k, U)) :
    (s2e_idealModule_sections_equiv k U x : Γ(B, U)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        k.toRingCatSheafHom)).val.app (op U) x := by
  let α := SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  let F := SheafOfModules.evaluation B.ringCatSheaf (op U)
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have he : (PreservesKernel.iso F α).hom ≫
      (ModuleCat.kernelIsoKer (F.map α)).hom ≫
        ModuleCat.ofHom (F.map α).hom.ker.subtype = F.map (kernel.ι α) := by
    rw [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  exact congrArg (fun f => f x) he

/-- Restricting an actual ideal section agrees with restricting its value
in the ambient structure sheaf. -/
theorem s2e_idealModule_sections_equiv_restrict
    {K B : Scheme.{0}} (k : K ⟶ B) {U V : B.Opens} (h : V ≤ U)
    (x : Γ(s2c_idealModule k, U)) :
    (s2e_idealModule_sections_equiv k V
      ((s2c_idealModule k).val.map (homOfLE h).op x) : Γ(B, V)) =
      B.presheaf.map (homOfLE h).op (s2e_idealModule_sections_equiv k U x) := by
  rw [s2e_idealModule_sections_equiv_coe, s2e_idealModule_sections_equiv_coe]
  exact congrArg (fun f => f x)
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)).val.naturality
      (homOfLE h).op)

/-- On an affine open the actual ideal module realizes the ideal data of
the same quasi-compact morphism. -/
def s2e_idealModule_affine_sections_equiv
    {K B : Scheme.{0}} (k : K ⟶ B) [QuasiCompact k] (U : B.affineOpens) :
    Γ(s2c_idealModule k, U) ≃ₗ[Γ(B, U)] k.ker.ideal U :=
  (s2e_idealModule_sections_equiv k U).trans
    (LinearEquiv.ofEq _ _ (k.ker_apply U).symm)

end HodgeLean.Foundations.Program
