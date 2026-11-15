import HodgeLean.Foundations.Program.SchoenTransferE1CupElementary
import HodgeLean.Foundations.Program.SchoenTransferE1Singleton

/-! The actual tensor generator in total degree zero. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The ordered tensor of the actual degree-zero cup units.
Source: Hatcher, Algebraic Topology, §3.2, the external cup unit. -/
def s4_e1_zeroTensorUnit
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    (h : ℕ) → s4_e1_tensor Y h (fun _ => 0)
  | 0 => (1 : ℚ)
  | h + 1 => unitClass Y ⊗ₜ[ℚ] s4_e1_zeroTensorUnit Y h

/-- Every tensor in the zero multidegree is a scalar multiple of the actual unit tensor.
Source: Hatcher, Algebraic Topology, §3.2; constants on a connected space. -/
theorem s4_e1_zeroTensor_spanned
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (z : s4_e1_tensor Y h (fun _ => 0)) :
    ∃ q : ℚ, q • s4_e1_zeroTensorUnit Y h = z := by
  induction h with
  | zero =>
      change ℚ at z
      exact ⟨z, by change z * 1 = z; exact mul_one z⟩
  | succ h ih =>
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, zero_smul _ _⟩
      | tmul x y =>
          obtain ⟨q, hq⟩ := (cupProductOf_zeroEquiv Y).surjective x
          have hqx : q • unitClass Y = x := hq
          obtain ⟨r, hr⟩ := ih y
          refine ⟨q * r, ?_⟩
          rw [← hqx, ← hr]
          change (q * r) • (unitClass Y ⊗ₜ[ℚ] s4_e1_zeroTensorUnit Y h) = _
          exact (TensorProduct.smul_tmul_smul q r (unitClass Y)
            (s4_e1_zeroTensorUnit Y h)).symm
      | add x y hx hy =>
          obtain ⟨q, hq⟩ := hx
          obtain ⟨r, hr⟩ := hy
          exact ⟨q + r, by rw [add_smul, hq, hr]; rfl⟩

/-- The zero multidegree has total degree zero. -/
theorem s4_e1_sum_zero (h : ℕ) : (∑ _ : Fin h, (0 : ℕ)) = 0 := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The actual ordered cup sends the tensor of units to the unit after its specified degree transport.
Source: Hatcher, Algebraic Topology, §3.2, naturality and the cup unit. -/
theorem s4_e1_orderedCup_zero_unit
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (h : ℕ) (f : Fin h → (T ⟶ Y)) :
    HQ.castEquiv T (s4_e1_sum_zero h)
      (s4_e1_orderedCup Y T h (fun _ => 0) f (s4_e1_zeroTensorUnit Y h)) =
      unitClass T := by
  induction h with
  | zero =>
      simp only [s4_e1_zeroTensorUnit, s4_e1_orderedCup, Fin.sum_univ_zero, id_eq]
      erw [HQ.castEquiv_apply_self, LinearMap.toSpanSingleton_apply]
      exact one_smul ℚ (unitClass T)
  | succ h ih =>
      rw [s4_e1_zeroTensorUnit, s4_e1_orderedCup_tmul,
        CupProduct.castEquiv_cup]
      have hu : homPullback (f 0) 0 (unitClass Y) = unitClass T :=
        spec_homPullback_unit (f 0)
      rw [hu]
      simp only [Fin.tail]
      erw [s4_e1_cup_cast_right T (s4_e1_sum_zero h) _ (show 0 + 0 = 0 from rfl)]
      erw [ih (Fin.tail f)]
      exact (cupProductOf T).one_cup (unitClass T)

#print axioms s4_e1_sum_zero
#print axioms s4_e1_orderedCup_zero_unit
#print axioms s4_e1_zeroTensorUnit
#print axioms s4_e1_zeroTensor_spanned
end HodgeLean.Foundations.Program
