import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso
import Mathlib.Data.Fintype.EquivFin

/-! # Actual global free frames for the stabilized middle module -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The original stabilized module has an actual sum-index global free frame. -/
def paired_free_biprod_unitIso (X : Scheme) (J : Type) :
    SheafOfModules.free (R := X.ringCatSheaf) (J ⊕ PUnit) ≅
      ((SheafOfModules.free (R := X.ringCatSheaf) J) ⊞
        SheafOfModules.unit X.ringCatSheaf) :=
  (SheafOfModules.freeSumIso (R := X.ringCatSheaf) J PUnit).symm ≪≫
    (biprod.isoCoprod _ _).symm ≪≫
    biprod.mapIso (Iso.refl _) (coproductUniqueIso
      (fun _ : PUnit => SheafOfModules.unit X.ringCatSheaf))

/-- Reindexing the actual global frame records its rank for fibre dimension calculations. -/
def paired_free_biprod_unitFinIso (X : Scheme) (k : ℕ) :
    SheafOfModules.free (R := X.ringCatSheaf) (Fin (k + 1)) ≅
      ((SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⊞
        SheafOfModules.unit X.ringCatSheaf) := by
  let e : Fin (k + 1) ≃ Fin k ⊕ PUnit :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin k ⊕ PUnit) = k + 1)).symm
  exact (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso ≪≫
    paired_free_biprod_unitIso X (Fin k)

/-- The actual stabilized free middle module is locally free. -/
theorem paired_free_biprod_unit_locallyFree (X : Scheme) (J : Type) :
    ((SheafOfModules.free (R := X.ringCatSheaf) J) ⊞
      SheafOfModules.unit X.ringCatSheaf).IsLocallyFree :=
  paired_module_locallyFree_of_iso (paired_free_biprod_unitIso X J)

end HodgeLean.Foundations.Program.G32Native
