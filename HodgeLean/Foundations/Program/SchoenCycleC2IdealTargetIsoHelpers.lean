import HodgeLean.Foundations.Program.SchoenCycleC2IdealIsoHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Transporting the ambient scheme through an isomorphism transports the
actual ideal module through its pushforward. -/
def s2e_idealModule_target_pushforward_iso
    {Q W W' : Scheme.{0}} (k : Q ⟶ W) (e : W ≅ W') :
    (Scheme.Modules.pushforward e.hom).obj (s2c_idealModule k) ≅
      s2c_idealModule (k ≫ e.hom) := by
  let F := Scheme.Modules.pushforward e.hom
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let η := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  let : IsIso η := s2e_structureModule_map_isIso e.hom
  let α := SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  let β := SheafOfModules.unitToPushforwardObjUnit (k ≫ e.hom).toRingCatSheafHom
  refine PreservesKernel.iso F α ≪≫ kernel.mapIso (F.map α) β (asIso η).symm
    ((Scheme.Modules.pushforwardComp k e.hom).app (SheafOfModules.unit Q.ringCatSheaf)) ?_
  change F.map α ≫ (Scheme.Modules.pushforwardComp k e.hom).hom.app
    (SheafOfModules.unit Q.ringCatSheaf) = inv η ≫ β
  apply (cancel_epi η).mp
  rw [IsIso.hom_inv_id_assoc]
  exact s2e_structureModule_map_comp k e.hom

end HodgeLean.Foundations.Program
