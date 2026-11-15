import HodgeLean.Foundations.Program.SchoenTransferJ12TopTensor
import HodgeLean.Foundations.Program.SchoenTransferE1

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The ordered product of the actual normalized curve top classes on its power is nonzero.
Source: injectivity of the actual curve-power Künneth map on the top tensor. -/
theorem s4_selected_curve_power_top_cup_ne_zero
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom] :
    s4_selected_divisor_cup (g3_power Y n) n
      (fun i => homPullback (g3_proj Y n i) 2 (I.symm 1)) ≠ 0 := by
  classical
  intro hz
  let J := {d : Fin n → ℕ // ∑ i, d i = 2 * n}
  let j : J := ⟨fun _ => 2, s4_selected_sum_two n⟩
  let z := s4_selected_top_tensor Y I n
  have hK : s4_e1_kunneth Y n (2 * n) (DirectSum.lof ℚ J _ j z) =
      s4_e1_kunneth Y n (2 * n) 0 := by
    rw [s4_e1_kunneth_component]
    change HQ.castEquiv (g3_power Y n) (s4_selected_sum_two n)
      (s4_e1_orderedCup Y (g3_power Y n) n (fun _ => 2) (g3_proj Y n) z) = _
    rw [s4_selected_ordered_top_tensor, hz, map_zero]
  have h0 := (s4_e1_power_kunneth Y hdim n (2 * n)).injective hK
  have hc := congrArg (DirectSum.component ℚ J (fun d => s4_e1_tensor Y n d.val) j) h0
  apply s4_selected_top_tensor_ne_zero Y I n
  calc
    z = (DirectSum.component ℚ J (fun d => s4_e1_tensor Y n d.val) j)
        ((DirectSum.lof ℚ J _ j) z) := (DirectSum.component.lof_self (M := fun d : J => s4_e1_tensor Y n d.val) ℚ j z).symm
    _ = (DirectSum.component ℚ J (fun d => s4_e1_tensor Y n d.val) j) 0 := hc
    _ = 0 := map_zero _

#print axioms s4_selected_curve_power_top_cup_ne_zero
end HodgeLean.Foundations.Program
