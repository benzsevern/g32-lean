import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Scalar extension along an algebra map is the tensor product with the
existing algebra structure. -/
def s2e_extendScalars_algebraMap_iso
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : ModuleCat A) :
    (ModuleCat.extendScalars (algebraMap A S)).obj M ≅ ModuleCat.of S (S ⊗[A] M) := by
  let S₀ := (ModuleCat.restrictScalars (algebraMap A S)).obj (ModuleCat.of S S)
  letI : Module S S₀ := inferInstanceAs (Module S S)
  let : IsScalarTower A S S₀ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e : S₀ ≃ₗ[S] S := LinearEquiv.refl S S
  exact (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl A M)).toModuleIso

end HodgeLean.Foundations.Program
