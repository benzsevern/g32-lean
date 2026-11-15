import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCup
import Mathlib.LinearAlgebra.Multilinear.Curry

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf

/-- The actual ordered divisor cup as a rational multilinear map.
Source: recursive currying of the actual bilinear cup product. -/
def s4_selected_divisor_cup_multilinear
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (n : ℕ) → MultilinearMap ℚ (fun _ : Fin n => HQ X 2) (HQ X (2 * n))
  | 0 => MultilinearMap.constOfIsEmpty ℚ _ (cupUnit X)
  | n + 1 => LinearMap.uncurryLeft
      { toFun := fun a => ((cupProductOf X).cup (by omega : 2 + 2 * n = 2 * (n + 1)) a).compMultilinearMap (s4_selected_divisor_cup_multilinear X n)
        map_add' := by
          intro a b
          ext v
          exact LinearMap.map_add₂ _ _ _ _
        map_smul' := by
          intro c a
          ext v
          exact LinearMap.map_smul₂ _ _ _ _ }

/-- Evaluating the multilinear divisor cup is the specified ordered divisor cup. -/
theorem s4_selected_divisor_cup_multilinear_apply
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (D : Fin n → HQ X 2) :
    s4_selected_divisor_cup_multilinear X n D = s4_selected_divisor_cup X n D := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cupProductOf X).cup (by omega : 2 + 2 * n = 2 * (n + 1)) (D 0)
      (s4_selected_divisor_cup_multilinear X n (Fin.tail D)) = _
    rw [ih]
    rfl

#print axioms s4_selected_divisor_cup_multilinear_apply
end HodgeLean.Foundations.Program
