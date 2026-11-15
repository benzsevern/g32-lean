import HodgeLean.Foundations.Program.G32Native.PairedConormalModuleFibres
import HodgeLean.Foundations.Curves.Picard.LineBundles.Transport
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Fibre dimension of the actual free presentation target -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- Canonical point coordinates of the actual unit-plus-free presentation target,
using the specified pullback and biproduct comparisons. -/
def conormalUnitFreeFibreCoordinates {X : Scheme.{0}}
    (x : Spec (CommRingCat.of ℂ) ⟶ X) (k : ℕ) :
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k)))) ≃ₗ[ℂ]
      (ℂ × (Fin k → ℂ)) := by
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  letI : G.IsRightAdjoint := ⟨_, ⟨tilde.adjunction⟩⟩
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts G
  let A := SheafOfModules.unit X.ringCatSheaf
  let B := SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  let eA := (G.mapIso (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x)).toLinearEquiv.trans i1_unitPointCoordinates
  let eB := (G.mapIso (SheafOfModules.pullbackObjFreeIso
    x.toRingCatSheafHom (Fin k))).toLinearEquiv.trans (i1_freePointCoordinates k)
  let e := (G.mapIso (F.mapBiprod A B) ≪≫ G.mapBiprod (F.obj A) (F.obj B) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv.trans (eA.prodCongr eB)
  exact e

/-- Pullback and global sections give the expected dimension of the specified
unit-plus-free target, with its actual biproduct retained. -/
theorem conormal_unit_free_target_fibre_finrank {X : Scheme.{0}}
    (x : Spec (CommRingCat.of ℂ) ⟶ X) (k : ℕ) :
    Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k)))) = k + 1 := by
  rw [(conormalUnitFreeFibreCoordinates x k).finrank_eq]
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
    Fintype.card_fin, mul_one, Nat.add_comm]

end HodgeLean.Foundations.Program.G32Native
