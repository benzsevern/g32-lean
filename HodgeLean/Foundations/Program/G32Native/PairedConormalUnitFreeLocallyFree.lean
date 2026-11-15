import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # Local freeness of the actual unit-plus-free presentation source -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual unit-plus-free presentation source is a free module, through
its specified coproduct and biproduct comparisons. -/
def conormalUnitFreeModuleIso (X : Scheme.{0}) (k : ℕ) :
    (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ≅
    SheafOfModules.free (R := X.ringCatSheaf) (PUnit ⊕ Fin k) := by
  let eUnit : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅
      SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit X.ringCatSheaf)
  exact biprod.isoCoprod _ _ ≪≫ coprod.mapIso eUnit.symm (Iso.refl _) ≪≫
    SheafOfModules.freeSumIso PUnit (Fin k)

/-- The supplied presentation source has local frames without a regularity premise. -/
theorem conormal_unit_free_locallyFree (X : Scheme.{0}) (k : ℕ) :
    (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.free (R := X.ringCatSheaf) (Fin k)).IsLocallyFree := by
  exact paired_module_locallyFree_of_iso (conormalUnitFreeModuleIso X k).symm

end HodgeLean.Foundations.Program.G32Native
