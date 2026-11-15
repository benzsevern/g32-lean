import HodgeLean.Foundations.Program.SchoenTransferCurveCharacterPairing
import HodgeLean.Foundations.Program.SchoenTransferComplexPullback
import HodgeLean.Foundations.Program.SchoenTransferCupPairVanishing
import HodgeLean.Foundations.Program.SchoenTransferMultilinearExpansion

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

variable (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (t : cyc_Field S.m →ₐ[ℚ] ℂ)

include hdim ha1 hamul

/-- Repeated coordinates vanish on an intrinsic primitive embedding space.
Source: Schoen (1988), Remark 1.4, p. 6. -/
theorem s4_repeated_coordinate_cup_zero
    (v : Fin h → s4_e2_curveSpace S Y a e t) (r : Fin h → Fin h)
    (hr : ¬ Function.Injective r) :
    (cupProductOf (g3_power Y h)).cupMultiC h
      (fun i => (homPullback (g3_proj Y h (r i)) 1).baseChange ℂ (v i)) = 0 := by
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hr
  apply s4_cupMultiC_zero_of_pair _ h _ i j hij
  rw [← heq, ← s4_complex_pullback_cup (g3_proj Y h (r i)) rfl]
  rw [s4_curve_character_pairing_zero S Y hdim a e ha1 hamul t
    (v i).property (v j).property, map_zero]

/-- Expanding the coordinate sum on one primitive embedding leaves precisely permutations.
Source: Schoen (1988), Remark 1.4, p. 6. -/
theorem s4_primitive_coordinate_expansion
    (v : Fin h → s4_e2_curveSpace S Y a e t) :
    (cupProductOf (g3_power Y h)).cupMultiC h
      (fun i => ∑ j, (homPullback (g3_proj Y h j) 1).baseChange ℂ (v i)) =
      ∑ σ : Equiv.Perm (Fin h), (cupProductOf (g3_power Y h)).cupMultiC h
        (fun i => (homPullback (g3_proj Y h (σ i)) 1).baseChange ℂ (v i)) := by
  apply multilinear_coordinate_expansion
  intro r hr
  exact s4_repeated_coordinate_cup_zero S Y hdim h a e ha1 hamul t v r hr

/-- The surviving coordinate assignments give the signed ordered-coordinate sum.
Source: Schoen (1988), Remark 1.4, p. 6; odd-degree permutation signs. -/
theorem s4_primitive_signed_coordinate_expansion
    (v : Fin h → s4_e2_curveSpace S Y a e t) :
    (cupProductOf (g3_power Y h)).cupMultiC h
      (fun i => ∑ j, (homPullback (g3_proj Y h j) 1).baseChange ℂ (v i)) =
      ∑ σ : Equiv.Perm (Fin h), σ.sign • (cupProductOf (g3_power Y h)).cupMultiC h
        (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ (v (σ i))) := by
  letI := (finbetti_finiteBetti (g3_power Y h)).finite 1
  rw [s4_primitive_coordinate_expansion S Y hdim h a e ha1 hamul t v]
  apply Fintype.sum_bijective (fun σ : Equiv.Perm (Fin h) => σ⁻¹)
    (inv_involutive.bijective) _ _
  intro σ
  have hp := s4_complex_cup_permutation (g3_power Y h) h
    (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ (v (σ⁻¹ i))) σ
  have hi : (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ (v (σ⁻¹ i))) ∘ σ =
      (fun i => (homPullback (g3_proj Y h (σ i)) 1).baseChange ℂ (v i)) := by
    funext i
    dsimp only [Function.comp_apply]
    rw [show σ⁻¹ (σ i) = i from σ.symm_apply_apply i]
  rw [hi] at hp
  simpa only [Equiv.Perm.sign_inv] using hp

end HodgeLean.Foundations.Program
