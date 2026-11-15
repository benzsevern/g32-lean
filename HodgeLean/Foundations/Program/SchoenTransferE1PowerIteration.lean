import HodgeLean.Foundations.Program.SchoenTransferE1PowerStep

/-! Iteration of the binary comparison on the specified ordered power maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.decEq Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- The binary step built from the actual smaller-power maps has the specified forward map.
Source: Hatcher, Algebraic Topology, §3.2, iteration of external cups. -/
theorem s4_e1_powerStepEquiv_eq
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (ih : ∀ n, Function.Bijective (s4_e1_kunneth Y h n)) (n : ℕ) :
    (s4_e1_powerStepEquiv Y h
      (fun n => LinearEquiv.ofBijective (s4_e1_kunneth Y h n) (ih n)) n).toLinearMap =
        s4_e1_kunneth Y (h + 1) n := by
  apply DirectSum.linearMap_ext ℚ
  rintro ⟨d, hd⟩
  subst n
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hs := s4_e1_powerStepEquiv_lof Y h
    (fun n => LinearEquiv.ofBijective (s4_e1_kunneth Y h n) (ih n))
    (∑ i, d i) ⟨d, rfl⟩ x y
  simp only [LinearEquiv.ofBijective_apply] at hs
  exact hs.trans (s4_e1_kunneth_succ_component Y h d x y).symm

/-- Every finite ordered power has the specified projection-cup decomposition.
Source: Hatcher, Algebraic Topology, §3.2, iteration of field-coefficient Künneth. -/
theorem s4_e1_power_kunneth_iteration
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h n : ℕ) : Function.Bijective (s4_e1_kunneth Y h n) := by
  induction h generalizing n with
  | zero => exact s4_e1_kunneth_empty Y n
  | succ h ih =>
      rw [← s4_e1_powerStepEquiv_eq Y h ih n]
      exact (s4_e1_powerStepEquiv Y h
        (fun n => LinearEquiv.ofBijective (s4_e1_kunneth Y h n) (ih n)) n).bijective

#print axioms s4_e1_powerStepEquiv_eq
#print axioms s4_e1_power_kunneth_iteration
end HodgeLean.Foundations.Program
