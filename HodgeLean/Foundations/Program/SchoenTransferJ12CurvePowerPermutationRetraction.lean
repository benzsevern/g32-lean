import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerLinearRetraction
import HodgeLean.Foundations.Program.SchoenTransferJ12PermutationCycles

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The unsigned geometric permutation sum of external odd cups is tensor alternation. -/
theorem s4_selected_curve_unsigned_sum_oneCup
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom] (v : Fin n → HQ Y 1) :
    ∑ σ : Equiv.Perm (Fin n), homPullback (s2_permute Y n σ) n
      (s4_e1_oneCup Y n (PiTensorProduct.tprod ℚ v)) =
      s4_e1_oneCup Y n
        (exteriorPower.toTensorPower ℚ (HQ Y 1) n (exteriorPower.ιMulti ℚ n v)) := by
  classical
  rw [exteriorPower.toTensorPower_apply_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [s4_e1_permutation_cup Y hdim n σ]
  simp only [Units.smul_def, map_zsmul, Int.cast_smul_eq_zsmul]

/-- The normalized retraction recovers the base cup from the unsigned geometric permutation sum. -/
theorem s4_selected_curve_power_retraction_unsigned_sum
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (L : HQ A 1 →ₗ[ℚ] HQ Y 1) (R : HQ Y 1 →ₗ[ℚ] HQ A 1)
    (hRL : R.comp L = LinearMap.id) (v : Fin n → HQ A 1) :
    s4_selected_curve_power_linear_retraction A Y hdim n R
      (∑ σ : Equiv.Perm (Fin n), homPullback (s2_permute Y n σ) n
        (s4_e1_oneCup Y n (PiTensorProduct.tprod ℚ (fun i => L (v i))))) =
      (cupProductOf A).cupMulti n v := by
  rw [s4_selected_curve_unsigned_sum_oneCup Y hdim]
  have h := LinearMap.congr_fun
    (s4_selected_curve_power_retraction_alternating A Y hdim n L R hRL)
    (exteriorPower.ιMulti ℚ n v)
  simpa only [LinearMap.comp_apply, exteriorPower.toTensorPower_apply_ιMulti,
    exteriorPower.map_apply_ιMulti, PiTensorProduct.map_tprod, map_sum,
    map_zsmul, Units.smul_def, CupProduct.cupWedgeMap_ιMulti] using h

#print axioms s4_selected_curve_unsigned_sum_oneCup
#print axioms s4_selected_curve_power_retraction_unsigned_sum
end HodgeLean.Foundations.Program
