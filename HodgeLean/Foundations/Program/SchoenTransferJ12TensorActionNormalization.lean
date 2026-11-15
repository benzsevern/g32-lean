import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerPermutationRetraction

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

/-- A specified tensor action evaluates the unsigned geometric permutation sum with its factorial.
Source: actual curve permutation cups and the tensor alternation factorial calculation. -/
theorem s4_selected_tensor_action_unsigned_sum
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (L : HQ A 1 →ₗ[ℚ] HQ Y 1) (R : HQ Y 1 →ₗ[ℚ] HQ A 1)
    (hRL : R.comp L = LinearMap.id)
    (E : HQ (g3_power Y n) n →ₗ[ℚ] HQ A n) (s : ℚ)
    (hE : E.comp (s4_e1_oneCup Y n) = s •
      (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
        (PiTensorProduct.map (fun _ : Fin n => R))) (v : Fin n → HQ A 1) :
    E (∑ σ : Equiv.Perm (Fin n), homPullback (s2_permute Y n σ) n
      (s4_e1_oneCup Y n (PiTensorProduct.tprod ℚ (fun i => L (v i))))) =
    (s * (Nat.factorial n : ℚ)) • (cupProductOf A).cupMulti n v := by
  classical
  rw [s4_selected_curve_unsigned_sum_oneCup Y hdim]
  have hrl (w : HQ A 1) : R (L w) = w := by
    have h := LinearMap.congr_fun hRL w
    exact h
  have ht : (PiTensorProduct.map (fun _ : Fin n => R))
      (exteriorPower.toTensorPower ℚ (HQ Y 1) n
        (exteriorPower.ιMulti ℚ n (fun i => L (v i)))) =
      exteriorPower.toTensorPower ℚ (HQ A 1) n (exteriorPower.ιMulti ℚ n v) := by
    rw [exteriorPower.toTensorPower_apply_ιMulti, map_sum,
      exteriorPower.toTensorPower_apply_ιMulti]
    simp only [Units.smul_def, map_zsmul, PiTensorProduct.map_tprod, hrl]
  have he := LinearMap.congr_fun hE
    (exteriorPower.toTensorPower ℚ (HQ Y 1) n
      (exteriorPower.ιMulti ℚ n (fun i => L (v i))))
  change E (s4_e1_oneCup Y n _) = s •
    PiTensorProduct.lift ((cupProductOf A).cupMulti n)
      ((PiTensorProduct.map (fun _ : Fin n => R)) _) at he
  rw [ht] at he
  have ha := LinearMap.congr_fun
    (tensor_alternation_factorial n ((cupProductOf A).cupAlternating n))
      (exteriorPower.ιMulti ℚ n v)
  change PiTensorProduct.lift ((cupProductOf A).cupMulti n)
    (exteriorPower.toTensorPower ℚ (HQ A 1) n (exteriorPower.ιMulti ℚ n v)) =
      (Nat.factorial n) • (cupProductOf A).cupWedgeMap n (exteriorPower.ιMulti ℚ n v) at ha
  rw [CupProduct.cupWedgeMap_ιMulti] at ha
  rw [ha, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul] at he
  exact he

#print axioms s4_selected_tensor_action_unsigned_sum
end HodgeLean.Foundations.Program
