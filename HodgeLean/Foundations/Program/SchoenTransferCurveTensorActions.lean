import HodgeLean.Foundations.Program.SchoenTransferComplexTensorAction
import HodgeLean.Foundations.Program.SchoenTransferTensorEigenSupport
import HodgeLean.Foundations.Program.SchoenTransferE1DeckRepresentation

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The zero deck tuple with a permutation is the specified coordinate permutation.
Source: Schoen (1988), §1, p. 5, the actual deck-permutation action. -/
theorem s4_zero_deck_permutation
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    s2_action S Y a e h 0 σ = s2_permute Y h σ := by
  apply s4_e1_power_hom_ext
  intro i
  rw [s4_e1_action_projection]
  change g3_proj Y h (σ.symm i) ≫ a (e.symm (.ofAdd 0)) = _
  rw [ofAdd_zero, map_one, ha1, Category.comp_id]
  exact (s4_e1_power_lift_projection h (fun k => g3_proj Y h (σ.symm k)) i).symm

/-- A single actual deck generator is the corresponding complex tensor coordinate operator.
Source: Schoen (1988), Lemma 1.2, pp. 5–6; the actual projection squares. -/
theorem s4_curve_tensor_coordinate_action
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (i : Fin h) :
    (homPullback (s2_action S Y a e h (Pi.single i 1) 1) h).baseChange ℂ ∘ₗ s4_complexOneCup Y h =
      s4_complexOneCup Y h ∘ₗ
        s4_tensorCoordinate ((homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ) i := by
  classical
  let b (j : Fin h) := a (e.symm (.ofAdd ((Pi.single i (1 : ZMod S.m) : Fin h → ZMod S.m) j)))
  have hu (j : Fin h) :
      s2_action S Y a e h (Pi.single i 1) 1 ≫ g3_proj Y h j = g3_proj Y h j ≫ b j := by
    have hp := s4_e1_action_projection S Y a e h (Pi.single i 1) 1 j
    change s2_action S Y a e h (Pi.single i 1) 1 ≫ g3_proj Y h j = g3_proj Y h j ≫ b j at hp
    exact hp
  rw [s4_complexOneCup_coordinate_action Y h _ b hu]
  congr 1
  unfold s4_tensorCoordinate
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [b, Pi.single_eq_same, Function.update_self]
  · simp only [b, Pi.single_eq_of_ne hj, ofAdd_zero, map_one, ha1,
      spec_homPullback_id, LinearMap.baseChange_id, Function.update_of_ne hj]

end HodgeLean.Foundations.Program
