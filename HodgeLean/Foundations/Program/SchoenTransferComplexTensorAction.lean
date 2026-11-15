import HodgeLean.Foundations.Program.SchoenTransferComplexOneCup
import HodgeLean.Foundations.Program.SchoenTransferAlternatingTensorRange
import HodgeLean.Foundations.Program.SchoenTransferE1CoordinateAction

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Coordinate squares identify the actual pullback with the specified complex tensor action.
Source: Hatcher, Algebraic Topology, §3.2, cup naturality; Schoen (1988), Lemma 1.2. -/
theorem s4_complexOneCup_coordinate_action
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (u : g3_power Y h ⟶ g3_power Y h) (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ g3_proj Y h i = g3_proj Y h i ≫ b i) :
    (homPullback u h).baseChange ℂ ∘ₗ s4_complexOneCup Y h =
      s4_complexOneCup Y h ∘ₗ PiTensorProduct.map
        (fun i => (homPullback (b i) 1).baseChange ℂ) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    s4_complexOneCup, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    PiTensorProduct.map_tprod]
  rw [s4_complex_pullback_cupMulti]
  congr 1
  funext i
  have he : homPullback u 1 ∘ₗ homPullback (g3_proj Y h i) 1 =
      homPullback (g3_proj Y h i) 1 ∘ₗ homPullback (b i) 1 := by
    rw [← spec_homPullback_comp, hu, spec_homPullback_comp]
  have heb := congrArg (LinearMap.baseChange ℂ) he
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at heb
  exact LinearMap.congr_fun heb (v i)

/-- Permutation pullback on the ordered complex tensor image has the degree-one sign.
Source: Schoen (1988), Lemma 1.2, p. 6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_complexOneCup_permutation_action
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (σ : Equiv.Perm (Fin h)) :
    (homPullback (s2_permute Y h σ) h).baseChange ℂ ∘ₗ s4_complexOneCup Y h =
      σ.sign • (s4_complexOneCup Y h ∘ₗ s4_tensorPermutation h σ) := by
  letI := (finbetti_finiteBetti (g3_power Y h)).finite 1
  have hp (i : Fin h) : s2_permute Y h σ ≫ g3_proj Y h i = g3_proj Y h (σ.symm i) :=
    s4_e1_power_lift_projection h _ i
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    s4_linearMap_unit_apply, s4_complexOneCup, s4_tensorPermutation,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.domDomCongr_apply]
  rw [s4_complex_pullback_cupMulti]
  have he (i : Fin h) :
      (homPullback (s2_permute Y h σ) 1).baseChange ℂ
        ((homPullback (g3_proj Y h i) 1).baseChange ℂ (v i)) =
        (homPullback (g3_proj Y h (σ.symm i)) 1).baseChange ℂ (v i) := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← spec_homPullback_comp, hp]
  simp only [he]
  have hs := s4_complex_cup_permutation (g3_power Y h) h
    (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ (v (σ i))) σ.symm
  have hv : (fun i => (homPullback (g3_proj Y h i) 1).baseChange ℂ (v (σ i))) ∘ σ.symm =
      (fun i => (homPullback (g3_proj Y h (σ.symm i)) 1).baseChange ℂ (v i)) := by
    funext i
    dsimp only [Function.comp_apply]
    rw [show σ (σ.symm i) = i from σ.apply_symm_apply i]
  rw [hv] at hs
  simpa only [Equiv.Perm.sign_symm] using hs

end HodgeLean.Foundations.Program
