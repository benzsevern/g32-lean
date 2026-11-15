import HodgeLean.Foundations.Program.G32Native.PairedC3ExtensionFrameAssembly
import Mathlib.CategoryTheory.Monoidal.Preadditive

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A specified inverse line frame turns the recursive negative bundle into a free bundle. -/
def pairedC3NegativeTensorFrame (k : ℕ) (L : (pairedC3Proj k).Modules)
    (e : pairedC3NegativeLine k ⊗ L ≅ 𝟙_ (pairedC3Proj k).Modules)
    (b : ℕ) : (pairedC3SplitBundle k 0 b ⊗ L) ≅ SheafOfModules.free (Fin b) := by
  let F := tensorRight (C := (pairedC3Proj k).Modules) L
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  induction b with
  | zero =>
    exact (Functor.map_isZero F (paired_c3_free_zero_isZero_nat k)).iso
      (paired_c3_free_zero_isZero_nat k)
  | succ b ih =>
    exact F.mapBiprod (pairedC3SplitBundle k 0 b) (pairedC3NegativeLine k) ≪≫
      biprod.mapIso ih e ≪≫
        (paired_free_biprod_unitFinIso (pairedC3Proj k) b).symm

end HodgeLean.Foundations.Program.G32Native
