import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.RingTheory.Ideal.Maps

/-! # Normalizing the first kernel map in module coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The kernel arrow before extending to the first component. -/
def unionConormalIdealKernelArrow
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    (p : R →+* A) (q : R →+* B) (J : Ideal R)
    (hP : RingHom.ker p = RingHom.ker q ⊓ J) :
    (ModuleCat.extendScalars (RingHom.id R)).obj (ModuleCat.of R (RingHom.ker p)) ⟶
      ModuleCat.of R (RingHom.ker q) :=
  (ModuleCat.extendScalarsId R).hom.app _ ≫
    ModuleCat.ofHom (Submodule.inclusion (hP ▸ inf_le_left))

/-- Unit tensor generators retain their ideal representatives under normalization. -/
lemma unionConormalIdealKernelArrow_one
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    (p : R →+* A) (q : R →+* B) (J : Ideal R)
    (hP : RingHom.ker p = RingHom.ker q ⊓ J) (x : RingHom.ker p) :
    ((unionConormalIdealKernelArrow p q J hP).hom ((1 : R) ⊗ₜ[R] x)).val = x.val := by
  change (Submodule.inclusion (hP ▸ inf_le_left)
    (((ModuleCat.extendScalarsId R).hom.app (ModuleCat.of R (RingHom.ker p))).hom ((1 : R) ⊗ₜ[R] x))).val = _
  rw [ModuleCat.extendScalarsId_hom_app_one_tmul]
  rfl

end HodgeLean.Foundations.Program.G32Native
