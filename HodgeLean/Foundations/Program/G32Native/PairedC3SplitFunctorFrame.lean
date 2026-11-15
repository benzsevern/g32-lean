import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Finite native frames through a specified additive functor -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A functor carrying the original free and negative summands to their
specified frames carries the recursive split bundle to the sum-rank frame. -/
def pairedC3SplitFunctorFrame (k a : ℕ) {Y : Scheme.{0}}
    (F : (pairedC3Proj k).Modules ⥤ Y.Modules)
    [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]
    (e₀ : F.obj (SheafOfModules.free (Fin a)) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin a))
    (eNeg : F.obj (pairedC3NegativeLine k) ≅
      SheafOfModules.unit Y.ringCatSheaf) (b : ℕ) :
    F.obj (pairedC3SplitBundle k a b) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (Fin (a + b)) := by
  induction b with
  | zero => exact e₀
  | succ b ih =>
    let e₁ : F.obj (pairedC3NegativeLine k) ≅
        SheafOfModules.free (R := Y.ringCatSheaf) (Fin 1) :=
      eNeg ≪≫ (coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit Y.ringCatSheaf)).symm
    exact F.mapBiprod _ _ ≪≫ biprod.mapIso ih e₁ ≪≫ biprod.isoCoprod _ _ ≪≫
      SheafOfModules.freeSumIso (Fin (a + b)) (Fin 1) ≪≫
      SheafOfModules.freeFunctor.mapIso finSumFinEquiv.toIso

#print axioms pairedC3SplitFunctorFrame
end HodgeLean.Foundations.Program.G32Native
