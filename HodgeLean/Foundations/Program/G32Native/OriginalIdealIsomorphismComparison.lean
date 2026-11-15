import HodgeLean.Foundations.Program.SchoenCycleC2IdealTargetIsoHelpers

/-! # Original ideal inclusions under source and ambient isomorphisms -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Changing source coordinates preserves the actual ideal inclusion.
Source: `s2e_idealModule_source_iso`, defined by `kernel.mapIso`. -/
theorem original_ideal_source_iso_inclusion
    {Q Q' W : Scheme.{0}} (j : Q ⟶ W) (e : Q' ≅ Q) :
    (s2e_idealModule_source_iso j e).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (e.hom ≫ j).toRingCatSheafHom) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) := by
  simp [s2e_idealModule_source_iso]

/-- Changing ambient coordinates preserves the actual ideal inclusion
through the canonical structure-module comparison.
Source: `s2e_idealModule_target_pushforward_iso`, `PreservesKernel.iso`,
and `kernel.mapIso`. -/
theorem original_ideal_target_iso_inclusion
    {Q W W' : Scheme.{0}} (j : Q ⟶ W) (e : W ≅ W') :
    letI := s2e_structureModule_map_isIso e.hom
    (s2e_idealModule_target_pushforward_iso j e).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ≫ e.hom).toRingCatSheafHom) =
      (Scheme.Modules.pushforward e.hom).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)) ≫
        inv (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom) := by
  letI := s2e_structureModule_map_isIso e.hom
  simp [s2e_idealModule_target_pushforward_iso, Category.assoc]

#print axioms original_ideal_source_iso_inclusion
#print axioms original_ideal_target_iso_inclusion
end HodgeLean.Foundations.Program
