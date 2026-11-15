import HodgeLean.Foundations.Program.SchoenTransferComplexCup

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The specified normalized coordinate map has the signed permutation numerator.
Source: Schoen (1988), Remark 1.4, p. 6; exterior-power scalar extension. -/
theorem s4_alternatingCup_coordinates
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (v : Fin h → ℂ ⊗[ℚ] HQ Y 1) :
    (Nat.factorial h : ℂ) • s4_e2_alternatingCup Y h (exteriorPower.ιMulti ℂ h v) =
      ∑ σ : Equiv.Perm (Fin h), σ.sign •
        (cupProductOf (g3_power Y h)).cupMultiC h
          (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ (v (σ i))) := by
  letI := (finbetti_finiteBetti Y).finite 1
  let B := ((cupProductOf (g3_power Y h)).cupMultiC h).compLinearMap
    (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ)
  let F := ((s4_e1_oneCup Y h).comp (exteriorPower.toTensorPower ℚ (HQ Y 1) h)).baseChange ℂ ∘ₗ
    (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := HQ Y 1) h).symm.toLinearMap
  have he : (F.compAlternatingMap (exteriorPower.ιMulti ℂ h)).toMultilinearMap =
      B.alternatization.toMultilinearMap := by
    let b := Module.finBasis ℚ (HQ Y 1)
    refine Module.Basis.ext_multilinear (fun _ => b.baseChange ℂ) fun σ => ?_
    simp only [Module.Basis.baseChange_apply, AlternatingMap.coe_multilinearMap,
      LinearMap.compAlternatingMap_apply, F, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← HodgeBlocks.complexifyWedge_ιMulti (V := HQ Y 1) h (fun i => b (σ i)),
      ← HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul,
      LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
    simp only [LinearMap.comp_apply, exteriorPower.toTensorPower_apply_ιMulti,
      map_sum, Units.smul_def, map_zsmul, s4_e1_oneCup, PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply, MultilinearMap.alternatization_apply,
      MultilinearMap.domDomCongr_apply, B, LinearMap.baseChange_tmul,
      CupProduct.cupMultiC_tmul, TensorProduct.tmul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    exact map_zsmul (TensorProduct.mk ℚ ℂ (HQ (g3_power Y h) h) 1) _ _
  have hev := congrFun (congrArg DFunLike.coe he) v
  have hc : (Nat.factorial h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)
  change (Nat.factorial h : ℂ) • ((Nat.factorial h : ℂ)⁻¹ • F (exteriorPower.ιMulti ℂ h v)) = _
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  simpa only [AlternatingMap.coe_multilinearMap, LinearMap.compAlternatingMap_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    B, MultilinearMap.compLinearMap_apply] using hev

end HodgeLean.Foundations.Program
