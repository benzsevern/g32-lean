import HodgeLean.Foundations.Program.SchoenTransferE1TensorAction
import HodgeLean.Foundations.Program.SchoenTransferE1CupElementary

/-! The binary recursion of the specified ordered projection cup. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 400000 in
/-- Splitting the first tensor factor gives the cup of the two actual projection pullbacks.
Source: Hatcher, Algebraic Topology, §3.2, naturality of external cup products. -/
theorem s4_e1_powerCup_succ
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    [IsIntegral (g3_power Y (h + 1)).left] [Smooth (g3_power Y (h + 1)).hom]
    [IsProjective (g3_power Y (h + 1)).hom]
    (d : Fin (h + 1) → ℕ) (x : HQ Y (d 0))
    (y : s4_e1_tensor Y h (Fin.tail d)) :
    s4_e1_orderedCup Y (g3_power Y (h + 1)) (h + 1) d (g3_proj Y (h + 1))
      (x ⊗ₜ[ℚ] y) =
    (cupProductOf (g3_power Y (h + 1))).cup (Fin.sum_univ_succ d).symm
      (homPullback (fst Y (g3_power Y h)) (d 0) x)
      (homPullback (snd Y (g3_power Y h)) (∑ i, Fin.tail d i)
        (s4_e1_orderedCup Y (g3_power Y h) h (Fin.tail d) (g3_proj Y h) y)) := by
  have ht := LinearMap.congr_fun
    (s4_e1_orderedCup_pullback Y (g3_power Y h) (g3_power Y (h + 1))
      (snd Y (g3_power Y h)) h (Fin.tail d) (g3_proj Y h)) y
  simp only [LinearMap.comp_apply] at ht
  rw [s4_e1_orderedCup_tmul]
  exact congrArg ((cupProductOf (g3_power Y (h + 1))).cup (Fin.sum_univ_succ d).symm
    (homPullback (fst Y (g3_power Y h)) (d 0) x)) ht.symm

#print axioms s4_e1_powerCup_succ
end HodgeLean.Foundations.Program
