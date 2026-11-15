import HodgeLean.Foundations.BundleResolution.IdealModuleTransportHelpers

/-! # Ambient direct-image transport retains the actual ideal inclusion

The kernel comparison uses the original structure-module isomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.BundleResolution

theorem i1_ambientIsoIdealPushforwardIso_inclusion {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsIso j] :
    (s2e_ambientIsoIdealPushforwardIso f j).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (f ≫ j).toRingCatSheafHom) ≫
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom =
    (Scheme.Modules.pushforward j).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  letI := s2e_unitPushforward_isIso j
  simp only [s2e_ambientIsoIdealPushforwardIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.lift_ι_assoc, Iso.symm_hom,
    IsIso.inv_hom_id, Category.comp_id]
  rw [PreservesKernel.iso_hom]
  simp only [asIso_inv, IsIso.inv_hom_id, Category.comp_id]
  exact kernelComparison_comp_ι _ _

end HodgeLean.Foundations.BundleResolution
