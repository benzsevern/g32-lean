import HodgeLean.Foundations.Program.SchoenTowerL1bKummerCyclicQuotient
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerOrbitDescent
import HodgeLean.Foundations.Program.SchoenTowerInertiaSuppliers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained original deck maps form the corresponding automorphism action. -/
def s2v_l1b_divisor_original_action
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) :
    (S.H ⧸ S.χ.ker) →* Aut Y where
  toFun g := Aut.of
    { hom := a g
      inv := a g⁻¹
      hom_inv_id := by rw [← hamul, inv_mul_cancel, ha1]
      inv_hom_id := by rw [← hamul, mul_inv_cancel, ha1] }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact ha1
  map_mul' u v := by
    apply Aut.ext
    apply Iso.ext
    exact hamul u v

end HodgeLean.Foundations.Program
