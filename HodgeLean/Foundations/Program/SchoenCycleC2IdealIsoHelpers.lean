import HodgeLean.Foundations.Program.SchoenCycleC2UnitCompositionHelpers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An isomorphism of the source retains the actual kernel-defined ideal
module in the ambient scheme. -/
def s2e_idealModule_source_iso
    {Q Q' W : Scheme.{0}} (k : Q ⟶ W) (e : Q' ≅ Q) :
    s2c_idealModule k ≅ s2c_idealModule (e.hom ≫ k) := by
  let η := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  let : IsIso η := s2e_structureModule_map_isIso e.hom
  let α := SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  let β := SheafOfModules.unitToPushforwardObjUnit (e.hom ≫ k).toRingCatSheafHom
  refine kernel.mapIso α β (Iso.refl _)
    ((Scheme.Modules.pushforward k).mapIso (asIso η) ≪≫
      (Scheme.Modules.pushforwardComp e.hom k).app (SheafOfModules.unit Q'.ringCatSheaf)) ?_
  change α ≫ (Scheme.Modules.pushforward k).map η ≫
      (Scheme.Modules.pushforwardComp e.hom k).hom.app
        (SheafOfModules.unit Q'.ringCatSheaf) = 𝟙 _ ≫ β
  rw [Category.id_comp]
  exact s2e_structureModule_map_comp e.hom k

end HodgeLean.Foundations.Program
