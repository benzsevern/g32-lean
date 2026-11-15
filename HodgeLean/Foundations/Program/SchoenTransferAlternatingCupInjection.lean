import HodgeLean.Foundations.Program.SchoenTransferE2ChainDefs
import HodgeLean.Foundations.Program.SchoenTransferAlternatingInjection

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The all-degree-one ordered cup map is injective on the specified tensor space.
Source: Hatcher, Algebraic Topology, §3.2, Künneth over a field. -/
theorem s4_oneCup_injective
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] : Function.Injective (s4_e1_oneCup Y h) := by
  rw [s4_e1_oneCup_kunneth_factor]
  intro x y hxy
  apply (s4_e1_oneTensorEquiv Y h).symm.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hxy
  have he := (s4_e1_power_kunneth Y hdim h h).injective hxy
  have hc := congrArg (DirectSum.component ℚ _ _
    ⟨fun _ : Fin h => 1, s4_e1_sum_one h⟩) he
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    DirectSum.component.lof_self] using hc

/-- The normalized alternating coordinate cup map is injective.
Source: Hatcher, Algebraic Topology, §3.2; Schoen (1988), Remark 1.4, p. 6. -/
theorem s4_alternatingCup_injective
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] : Function.Injective (s4_e2_alternatingCup Y h) := by
  letI := (finbetti_finiteBetti Y).finite 1
  have hi : Function.Injective ((s4_e1_oneCup Y h).comp
      (exteriorPower.toTensorPower ℚ (HQ Y 1) h)) :=
    (s4_oneCup_injective Y hdim h).comp (tensor_alternation_injective h)
  have hib : Function.Injective (((s4_e1_oneCup Y h).comp
      (exteriorPower.toTensorPower ℚ (HQ Y 1) h)).baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hi
  have hc : (Nat.factorial h : ℂ)⁻¹ ≠ 0 := inv_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h))
  intro x y hxy
  apply (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := HQ Y 1) h).symm.injective
  apply hib
  exact (smul_right_injective _ hc) hxy

end HodgeLean.Foundations.Program
