import HodgeLean.Foundations.Program.SchoenTransferE1CupElementary
import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Ordered tensor of the specified normalized curve top class.
Source: the actual degree-two rational coordinate on the curve. -/
def s4_selected_top_tensor
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) : (n : ℕ) → s4_e1_tensor Y n (fun _ => 2)
  | 0 => (1 : ℚ)
  | n + 1 => I.symm 1 ⊗ₜ[ℚ] s4_selected_top_tensor Y I n

/-- The tensor coordinate induced by the specified curve top coordinate.
Source: the tensor product of the actual degree-two coordinates. -/
def s4_selected_top_tensor_equiv
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) : (n : ℕ) → s4_e1_tensor Y n (fun _ => 2) ≃ₗ[ℚ] ℚ
  | 0 => LinearEquiv.refl ℚ ℚ
  | n + 1 => (TensorProduct.congr I (s4_selected_top_tensor_equiv Y I n)).trans
      (TensorProduct.lid ℚ ℚ)

/-- The actual normalized top tensor has coordinate one. -/
theorem s4_selected_top_tensor_coordinate
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (n : ℕ) :
    s4_selected_top_tensor_equiv Y I n (s4_selected_top_tensor Y I n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change I (I.symm 1) * s4_selected_top_tensor_equiv Y I n
      (s4_selected_top_tensor Y I n) = 1
    rw [LinearEquiv.apply_symm_apply, ih, mul_one]

/-- The actual normalized top tensor is nonzero. -/
theorem s4_selected_top_tensor_ne_zero
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (n : ℕ) : s4_selected_top_tensor Y I n ≠ 0 := by
  intro h
  have hh := s4_selected_top_tensor_coordinate Y I n
  rw [h, map_zero] at hh
  exact zero_ne_one hh

/-- The total degree of the ordered curve top tensor. -/
theorem s4_selected_sum_two (n : ℕ) : (∑ _ : Fin n, (2 : ℕ)) = 2 * n := by simp [Nat.mul_comm]

/-- Actual ordered coordinate cups send the top tensor to the ordered top divisor cup.
Source: the recursive external cup maps and their specified degree transports. -/
theorem s4_selected_ordered_top_tensor
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (n : ℕ) (f : Fin n → (T ⟶ Y)) :
    HQ.castEquiv T (s4_selected_sum_two n)
      (s4_e1_orderedCup Y T n (fun _ => 2) f (s4_selected_top_tensor Y I n)) =
    s4_selected_divisor_cup T n (fun i => homPullback (f i) 2 (I.symm 1)) := by
  induction n with
  | zero =>
    change (1 : ℚ) • cupUnit T = cupUnit T
    exact one_smul _ _
  | succ n ih =>
    rw [s4_selected_top_tensor, s4_e1_orderedCup_tmul, CupProduct.castEquiv_cup]
    dsimp only [Fin.tail]
    rw [s4_e1_cup_cast_right T (s4_selected_sum_two n) _ (by omega : 2 + 2 * n = 2 * (n + 1))]
    exact congrArg ((cupProductOf T).cup (by omega : 2 + 2 * n = 2 * (n + 1))
      (homPullback (f 0) 2 (I.symm 1))) (ih (Fin.tail f))

#print axioms s4_selected_top_tensor_ne_zero
#print axioms s4_selected_ordered_top_tensor
end HodgeLean.Foundations.Program
