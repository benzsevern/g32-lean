import HodgeLean.Foundations.Curves.AbelTheorem.Defs

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

theorem transverse_path_reparam (γ : b3_SmoothLoop E C) (δ : ℝ → C)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ)
    (htr : ∀ s t, γ.val s = δ t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C δ t) ≠ 0)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 1 σ)
    (hder : ∀ s t, γ.val s = δ (σ t) → deriv σ t ≠ 0) :
    ∀ s t, γ.val s = (δ ∘ σ) t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C (δ ∘ σ) t) ≠ 0 := by
  intro s t he
  have hv := b3A_velocity_reparam δ hδ σ (hσ.differentiable (by simp)) t
  change b3_velocity E C (δ ∘ σ) t = ((deriv σ t : ℝ) : ℂ) • b3_velocity E C δ (σ t) at hv
  rw [hv]
  exact (b3A_orient_smul_right (E := E) (b3_velocity E C γ.val s)
    (b3_velocity E C δ (σ t)) (deriv σ t)).trans_ne
      (mul_ne_zero (hder s t he) (htr s (σ t) he))

end HodgeLean.Foundations.Curves.AbelTheorem
