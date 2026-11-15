import HodgeLean.Foundations.Curves.AbelTheorem.TransverseReparam

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem transverse_step_path (γ : b3_SmoothLoop E C) (δ : ℝ → C)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ)
    (htr : ∀ s t, γ.val s = δ t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C δ t) ≠ 0)
    (hends : ∀ s, γ.val s ≠ δ 0 ∧ γ.val s ≠ δ 1) :
    ∀ s t, γ.val s = (δ ∘ b3A_step) t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C (δ ∘ b3A_step) t) ≠ 0 := by
  apply transverse_path_reparam γ δ hδ htr b3A_step b3A_step_contDiff
  intro s t he
  have hzero : b3A_step t ≠ 0 := by
    intro hz
    exact (hends s).1 (by simpa only [hz] using he)
  have hone : b3A_step t ≠ 1 := by
    intro hz
    exact (hends s).2 (by simpa only [hz] using he)
  have h0 : 0 < 3 * t - 1 := by
    by_contra hn
    exact hzero (Real.smoothTransition.zero_of_nonpos (not_lt.mp hn))
  have h1 : 3 * t - 1 < 1 := by
    by_contra hn
    exact hone (Real.smoothTransition.one_of_one_le (not_lt.mp hn))
  obtain ⟨d, hd, hder⟩ := b3Rest_smoothTransition_hasDerivAt_pos ⟨h0, h1⟩
  have hstep : HasDerivAt b3A_step (d * 3) t := by
    convert hder.comp t (((hasDerivAt_id t).const_mul 3).sub_const 1) using 1 <;>
      first | rfl | ring
  rw [hstep.deriv]
  exact mul_ne_zero hd.ne' (by norm_num)

end HodgeLean.Foundations.Curves.AbelTheorem
