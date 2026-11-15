import HodgeLean.Foundations.Program.SchoenTransferE1CupElementary

/-! Compatibility of the indexed and recursively ordered degree-one cup maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- Ordered projection cups agree with the actual multilinear cup on pure tensors.
Source: Hatcher, Algebraic Topology, §3.2, the ordered external cup product. -/
theorem s4_e1_orderedCup_one_pure
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (h : ℕ) (f : Fin h → (T ⟶ Y)) (v : Fin h → HQ Y 1) :
    HQ.castEquiv T (s4_e1_sum_one h)
      (s4_e1_orderedCup Y T h (fun _ => 1) f
        ((s4_e1_oneTensorEquiv Y h).symm (PiTensorProduct.tprod ℚ v))) =
      (cupProductOf T).cupMulti h (fun i => homPullback (f i) 1 (v i)) := by
  induction h with
  | zero =>
      change PiTensorProduct.isEmptyEquiv (R := ℚ)
        (s := fun _ : Fin 0 => HQ Y 1) (Fin 0) (PiTensorProduct.tprod ℚ v) •
          cupUnit T = cupUnit T
      rw [PiTensorProduct.isEmptyEquiv_apply_tprod, one_smul]
  | succ h ih =>
      rw [s4_e1_oneTensorEquiv_symm_tprod]
      rw [s4_e1_orderedCup_tmul]
      dsimp only [Fin.tail]
      rw [CupProduct.castEquiv_cup,
        s4_e1_cup_cast_right T (s4_e1_sum_one h) _ (Nat.add_comm 1 h)]
      exact congrArg
        ((cupProductOf T).cup (Nat.add_comm 1 h) (homPullback (f 0) 1 (v 0)))
        (ih (Fin.tail f) (Fin.tail v))

#print axioms s4_e1_sum_one
#print axioms s4_e1_cup_cast_right
#print axioms s4_e1_orderedCup_one_pure
end HodgeLean.Foundations.Program
