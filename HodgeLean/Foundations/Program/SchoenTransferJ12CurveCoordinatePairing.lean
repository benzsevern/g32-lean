import HodgeLean.Foundations.Program.SchoenTransferJ12CupMultiPair
import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCupScalars

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Pairing actual coordinate cups separates into the curve pairings and one top coordinate.
Source: the degree-two curve coordinate and the signed ordered cup pairing. -/
theorem s4_selected_curve_coordinate_pairing
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (n : ℕ) (f : Fin n → (T ⟶ Y)) (IY : HQ Y 2 ≃ₗ[ℚ] ℚ)
    (IT : HQ T (2 * n) →ₗ[ℚ] ℚ) (v u : Fin n → HQ Y 1) :
    IT ((cupProductOf T).cup (by omega : n + n = 2 * n)
      ((cupProductOf T).cupMulti n (fun i => homPullback (f i) 1 (v i)))
      ((cupProductOf T).cupMulti n (fun i => homPullback (f i) 1 (u i)))) =
    ((-1 : ℚ) ^ n.choose 2) *
      (∏ i, IY ((cupProductOf Y).cup rfl (v i) (u i))) *
      IT (s4_selected_divisor_cup T n (fun i => homPullback (f i) 2 (IY.symm 1))) := by
  have hz (z : HQ Y 2) : z = IY z • IY.symm 1 := by
    apply IY.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hD : (fun i => (cupProductOf T).cup rfl
      (homPullback (f i) 1 (v i)) (homPullback (f i) 1 (u i))) =
      (fun i => IY ((cupProductOf Y).cup rfl (v i) (u i)) •
        homPullback (f i) 2 (IY.symm 1)) := by
    funext i
    rw [← spec_homPullback_cup]
    conv_lhs => arg 2; rw [hz ((cupProductOf Y).cup rfl (v i) (u i))]
    exact (homPullback (f i) 2).map_smul _ _
  rw [s4_selected_cup_multi_pair, hD, s4_selected_divisor_cup_scalars]
  simp only [map_smul, smul_eq_mul]
  exact (mul_assoc _ _ _).symm

#print axioms s4_selected_curve_coordinate_pairing
end HodgeLean.Foundations.Program
