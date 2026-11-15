import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCup
import HodgeLean.Foundations.Program.SchoenTransferPairing

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

/-- Pairing two ordered degree-one cups gives the signed ordered product of their paired factors.
Source: graded commutativity, with one exchange for each preceding factor. -/
theorem s4_selected_cup_multi_pair
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (a b : Fin n → HQ X 1) :
    (cupProductOf X).cup (by omega : n + n = 2 * n)
      ((cupProductOf X).cupMulti n a) ((cupProductOf X).cupMulti n b) =
    ((-1 : ℚ) ^ n.choose 2) • s4_selected_divisor_cup X n
      (fun i => (cupProductOf X).cup rfl (a i) (b i)) := by
  induction n with
  | zero =>
    rw [CupProduct.cupMulti_zero, CupProduct.cupMulti_zero]
    change (cupProductOf X).cup (by omega : 0 + 0 = 0) (unitClass X) (unitClass X) =
      (1 : ℚ) • unitClass X
    rw [one_smul]
    exact (cupProductOf X).cup_one (unitClass X)
  | succ n ih =>
    rw [CupProduct.cupMulti_succ _ n (by omega), CupProduct.cupMulti_succ _ n (by omega)]
    rw [s4_cup_middle_exchange X (cupProductOf X) 1 n 1 n (n + 1) (n + 1)
      2 (2 * n) (2 * (n + 1)) (by omega) (by omega) rfl (by omega) (by omega)]
    rw [ih, map_smul, smul_smul]
    change _ • s4_selected_divisor_cup X (n + 1) (fun i =>
      (cupProductOf X).cup rfl (a i) (b i)) = _
    congr 1
    simp only [Nat.mul_one, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

#print axioms s4_selected_cup_multi_pair
end HodgeLean.Foundations.Program
