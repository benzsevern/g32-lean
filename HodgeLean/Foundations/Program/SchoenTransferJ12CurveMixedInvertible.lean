import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedContraction
import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePairing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- A nondegenerate mixed divisor acts invertibly when the curve map identifies degree one. -/
theorem s4_selected_curve_mixed_action_bijective
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (hf : Function.Bijective (homPullback f 1))
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (ω : ⋀[ℚ]^2 (HQ A 1))
    (hω : Symplectic.IsNondegenerate ω) :
    Function.Bijective (s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num)
      (s4_selected_curve_mixed_divisor A Y f ((cupProductOf A).cupWedgeMap 2 ω))) := by
  let P := ((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂ I.toLinearMap
  have hP : Function.Bijective P := s4_selected_curve_pairing_bijective Y hdim I
  have hflip (v : HQ Y 1) : P.flip v = -P v := by
    ext w
    change I ((cupProductOf Y).cup rfl w v) = -I ((cupProductOf Y).cup rfl v w)
    rw [CupProduct.cup_comm_one, map_neg]
  have hPf : Function.Bijective P.flip := by
    constructor
    · intro v w h
      rw [hflip, hflip, neg_inj] at h
      exact hP.injective h
    · intro φ
      obtain ⟨v, hv⟩ := hP.surjective (-φ)
      exact ⟨v, by rw [hflip, hv, neg_neg]⟩
  let C : HQ Y 1 →ₗ[ℚ] Module.Dual ℚ (HQ A 1) :=
    (homPullback f 1).dualMap.comp P.flip
  have hC : Function.Bijective C :=
    (LinearMap.dualMap_bijective_iff.mpr hf).comp hPf
  constructor
  · intro u v h
    rw [s4_selected_curve_mixed_action_contract, s4_selected_curve_mixed_action_contract,
      neg_inj] at h
    exact hC.injective (hω.injective h)
  · intro v
    obtain ⟨φ, hφ⟩ := hω.surjective (-v)
    obtain ⟨u, hu⟩ := hC.surjective φ
    refine ⟨u, ?_⟩
    rw [s4_selected_curve_mixed_action_contract]
    change -Symplectic.contract ω (C u) = v
    rw [hu, hφ, neg_neg]

#print axioms s4_selected_curve_mixed_action_bijective
end HodgeLean.Foundations.Program
