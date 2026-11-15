import HodgeLean.Foundations.Program.SchoenTowerConormalDefs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The actual structure-module maps compose with the scheme morphisms. -/
theorem s2e_structureModule_map_comp
    {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext r
  rfl

/-- A scheme isomorphism induces an invertible structure-module map. -/
theorem s2e_structureModule_map_isIso
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (f.app U)
  exact ConcreteCategory.bijective_of_isIso (f.app U)

end HodgeLean.Foundations.Program
