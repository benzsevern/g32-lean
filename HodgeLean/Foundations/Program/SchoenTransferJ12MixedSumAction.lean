import HodgeLean.Foundations.Program.SchoenTransferJ12MixedSumCupAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual mixed product action retracts the full cohomology degree of sum pullback up to its specified scalar.
Source: the cup calculation and the actual exterior presentation of abelian cohomology. -/
theorem s4_selected_mixed_sum_action
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (f g : Y ⟶ A) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (IY : HQ Y 2 ≃ₗ[ℚ] ℚ) (IT : HQ (g3_power Y n) (2 * n) ≃ₗ[ℚ] ℚ)
    (pol : HQ A 2) (c : ℚ) (hc : c ≠ 0)
    (hact : (s4_selected_corr_action A Y 1 IY 1 1 1 (by omega)
      (s4_selected_curve_mixed_divisor A Y g pol)).comp (homPullback f 1) = c • LinearMap.id)
    : (s4_selected_corr_action A (g3_power Y n) n IT n n n (by omega)
      (s4_selected_mixed_divisor_kernel A (g3_power Y n) n
        (fun i => g3_proj Y n i ≫ g) pol)).comp (homPullback (s4_sum f n) n) =
    ((IT (s4_selected_divisor_cup (g3_power Y n) n
      (fun i => homPullback (g3_proj Y n i) 2 (IY.symm 1))) * c ^ n) *
        (Nat.factorial n : ℚ)) • LinearMap.id := by
  let H := (s4_selected_corr_action A (g3_power Y n) n IT n n n (by omega)
    (s4_selected_mixed_divisor_kernel A (g3_power Y n) n
      (fun i => g3_proj Y n i ≫ g) pol)).comp (homPullback (s4_sum f n) n)
  let s := (IT (s4_selected_divisor_cup (g3_power Y n) n
    (fun i => homPullback (g3_proj Y n i) 2 (IY.symm 1))) * c ^ n) *
      (Nat.factorial n : ℚ)
  have hH : H.comp ((cupProductOf A).cupWedgeMap n) = s • (cupProductOf A).cupWedgeMap n := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, CupProduct.cupWedgeMap_ιMulti, H, s] using
      s4_selected_mixed_sum_cup_action A Y hdim f g n IY IT pol c hc hact v
  ext x
  obtain ⟨w, rfl⟩ := ((torusCohomology_cupProductOf A).cupWedgeEquiv n).surjective x
  exact LinearMap.congr_fun hH w

#print axioms s4_selected_mixed_sum_action
end HodgeLean.Foundations.Program
