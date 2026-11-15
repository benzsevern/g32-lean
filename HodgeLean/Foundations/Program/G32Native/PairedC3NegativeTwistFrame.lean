import HodgeLean.Foundations.Program.G32Native.PairedC3SplitFunctorFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3DualTensorIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # The finite free frame of the original positively twisted negative sum -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The positive native line cancels every actual negative summand,
including the zero-rank endpoint, in the original recursive bundle. -/
def pairedC3NegativeSumTwistFrame (k b : ℕ) :
    pairedC3SplitBundle k 0 b ⊗ ProjSpace.twistingSheaf ℂ k ≅
      SheafOfModules.free (R := (pairedC3Proj k).ringCatSheaf) (Fin b) := by
  let L := ProjSpace.twistingSheaf ℂ k
  let F := tensorRight L
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have h₀ : IsZero (SheafOfModules.free (R := (pairedC3Proj k).ringCatSheaf) (Fin 0)) := by
    rw [IsZero.iff_id_eq_zero]
    apply (SheafOfModules.freeHomEquiv _ (I := Fin 0)).injective
    funext j
    exact Fin.elim0 j
  let e₀ : F.obj (SheafOfModules.free (Fin 0)) ≅
      SheafOfModules.free (R := (pairedC3Proj k).ringCatSheaf) (Fin 0) :=
    (F.map_isZero h₀).iso h₀
  let eN : F.obj (pairedC3NegativeLine k) ≅
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf :=
    (β_ (pairedC3NegativeLine k) L) ≪≫
      pairedC3DualTensorIso (ProjSpace.isInvertible_twistingSheaf ℂ k)
  exact pairedC3SplitFunctorFrame k 0 F e₀ eN b ≪≫ eqToIso (by rw [Nat.zero_add])

#print axioms pairedC3NegativeSumTwistFrame
end HodgeLean.Foundations.Program.G32Native
