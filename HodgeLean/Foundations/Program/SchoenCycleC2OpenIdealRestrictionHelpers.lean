import HodgeLean.Foundations.Program.SchoenCycleC2OpenPushforwardUnitHelpers
import HodgeLean.Foundations.Algebraic.GrassmannianSheafRestrict
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The open-restriction identification intertwines the actual two
structure-module maps. -/
theorem s2e_open_restrict_pushforward_unit_map
    {Q W : Scheme.{0}} (k : Q ⟶ W) (U : W.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map
        (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
      (s2e_open_restrict_pushforward_unit_iso k U).hom =
    (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      SheafOfModules.unitToPushforwardObjUnit (k ∣_ U).toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext r
  change Q.presheaf.map (eqToHom (image_morphismRestrict_preimage k U V.unop)).op
      (k.app (U.ι ''ᵁ V.unop) r) =
    (k ∣_ U).app V.unop ((U.ι.appIso V.unop).hom r)
  rw [U.ι_appIso]
  change Q.presheaf.map (eqToHom (image_morphismRestrict_preimage k U V.unop)).op
      (k.app (U.ι ''ᵁ V.unop) r) = (k ∣_ U).app V.unop r
  rw [morphismRestrict_app]
  rfl

/-- The actual kernel-defined ideal module restricts to the ideal module
of the actual restricted morphism. -/
def s2e_idealModule_restrict_iso
    {Q W : Scheme.{0}} (k : Q ⟶ W) (U : W.Opens) :
    Scheme.Modules.restrict (s2c_idealModule k) U.ι ≅ s2c_idealModule (k ∣_ U) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let α := SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  let β := SheafOfModules.unitToPushforwardObjUnit (k ∣_ U).toRingCatSheafHom
  exact PreservesKernel.iso F α ≪≫ kernel.mapIso (F.map α) β
    (Scheme.Modules.restrictUnitIso U.ι) (s2e_open_restrict_pushforward_unit_iso k U)
    (s2e_open_restrict_pushforward_unit_map k U)

end HodgeLean.Foundations.Program
