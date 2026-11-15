import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Original coordinate projections on finite free sheaves -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native

/-- The coordinate functional on the original coproduct presentation. -/
def paired_freeCoordinateProjection {C : Type*} [Category* C]
    {T : GrothendieckTopology C} (R : Sheaf T RingCat)
    [HasWeakSheafify T AddCommGrpCat] [T.WEqualsLocallyBijective AddCommGrpCat]
    {J : Type} [DecidableEq J] (j : J) :
    SheafOfModules.free (R := R) J ⟶ SheafOfModules.unit R :=
  Sigma.desc (fun i => if i = j then 𝟙 _ else 0)

/-- The selected coordinate is retained with coefficient one. -/
theorem paired_freeCoordinateProjection_self {C : Type*} [Category* C]
    {T : GrothendieckTopology C} (R : Sheaf T RingCat)
    [HasWeakSheafify T AddCommGrpCat] [T.WEqualsLocallyBijective AddCommGrpCat]
    {J : Type} [DecidableEq J] (j : J) :
    SheafOfModules.ιFree j ≫ paired_freeCoordinateProjection R j = 𝟙 _ := by
  unfold paired_freeCoordinateProjection SheafOfModules.ιFree
  exact (Sigma.ι_comp_desc (fun i : J => if i = j then 𝟙 _ else 0) j).trans
    (if_pos rfl)

/-- Distinct original coordinates have coefficient zero. -/
theorem paired_freeCoordinateProjection_other {C : Type*} [Category* C]
    {T : GrothendieckTopology C} (R : Sheaf T RingCat)
    [HasWeakSheafify T AddCommGrpCat] [T.WEqualsLocallyBijective AddCommGrpCat]
    {J : Type} [DecidableEq J] (i j : J) (hij : i ≠ j) :
    SheafOfModules.ιFree i ≫ paired_freeCoordinateProjection R j = 0 := by
  unfold paired_freeCoordinateProjection SheafOfModules.ιFree
  exact (Sigma.ι_comp_desc (fun l : J => if l = j then 𝟙 _ else 0) i).trans
    (if_neg hij)

end HodgeLean.Foundations.Program.G32Native
