import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
attribute [local instance] b3Forms_isManifold_real

theorem finite_transverse_crossings_in_box (γ δ : ℝ → C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ)
    (htr : ∀ s t, γ s = δ t →
      b3_orient E (b3_velocity E C γ s) (b3_velocity E C δ t) ≠ 0)
    (a b c d : ℝ) :
    {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ q.2 ∈ Icc c d ∧ γ q.1 = δ q.2}.Finite := by
  let S := (Icc a b ×ˢ Icc c d) ∩ {q : ℝ × ℝ | γ q.1 = δ q.2}
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_eq (hγ.continuous.comp continuous_fst) (hδ.continuous.comp continuous_snd))
  have hdisc : IsDiscrete S := by
    rw [isDiscrete_iff_nhdsNE]
    intro q hq
    rw [inf_principal_eq_bot]
    filter_upwards [b3A_crossing_isolated γ δ hγ hδ q.1 q.2 hq.2 (htr _ _ hq.2)]
      with u hu huS
    exact hu huS.2
  exact (hS.finite hdisc).subset fun q hq => ⟨⟨hq.1, hq.2.1⟩, hq.2.2⟩

end HodgeLean.Foundations.Curves.AbelTheorem
