import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCup
import HodgeLean.Foundations.Program.SchoenTransferPairing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The product of degree-one external crosses has the specified permutation sign.
Source: repeated exchange of the middle factors in the actual graded cup product. -/
theorem s4_selected_cross_cup_product
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) (a : Fin n → HQ A 1) (b : Fin n → HQ Y 1) :
    s4_selected_divisor_cup (A ⊗ Y) n (fun i =>
      (cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (fst A Y) 1 (a i)) (homPullback (snd A Y) 1 (b i))) =
    ((-1 : ℚ) ^ n.choose 2) • (cupProductOf (A ⊗ Y)).cup (by omega : n + n = 2 * n)
      (homPullback (fst A Y) n ((cupProductOf A).cupMulti n a))
      (homPullback (snd A Y) n ((cupProductOf Y).cupMulti n b)) := by
  induction n with
  | zero =>
    rw [CupProduct.cupMulti_zero, CupProduct.cupMulti_zero]
    change cupUnit (A ⊗ Y) = (1 : ℚ) • (cupProductOf (A ⊗ Y)).cup (by omega : 0 + 0 = 0)
      (homPullback (fst A Y) 0 (cupUnit A)) (homPullback (snd A Y) 0 (cupUnit Y))
    rw [one_smul, spec_homPullback_unit, spec_homPullback_unit]
    exact ((cupProductOf (A ⊗ Y)).cup_one (unitClass (A ⊗ Y))).symm
  | succ n ih =>
    change (cupProductOf (A ⊗ Y)).cup (by omega : 2 + 2 * n = 2 * (n + 1))
      ((cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (fst A Y) 1 (a 0)) (homPullback (snd A Y) 1 (b 0)))
      (s4_selected_divisor_cup (A ⊗ Y) n (fun i =>
        (cupProductOf (A ⊗ Y)).cup rfl
          (homPullback (fst A Y) 1 (a i.succ))
          (homPullback (snd A Y) 1 (b i.succ)))) = _
    rw [ih, map_smul]
    rw [s4_cup_middle_exchange (A ⊗ Y) (cupProductOf (A ⊗ Y))
      1 1 n n 2 (2 * n) (n + 1) (n + 1) (2 * (n + 1))
      rfl (by omega) (by omega) (by omega) (by omega)]
    rw [← spec_homPullback_cup (fst A Y), ← spec_homPullback_cup (snd A Y)]
    rw [CupProduct.cupMulti_succ _ n (by omega), CupProduct.cupMulti_succ _ n (by omega)]
    simp only [Fin.tail, Nat.one_mul, smul_smul]
    congr 1
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    exact mul_comm _ _

#print axioms s4_selected_cross_cup_product
end HodgeLean.Foundations.Program
