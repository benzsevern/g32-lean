import HodgeLean.Foundations.Curves.AbelTheorem.FiniteTransverseLocalPath

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem finite_transverse_path_neighborhood (h : Module.finrank ℂ E = 1)
    {ι : Type} [Fintype ι] (γ : ι → b3_SmoothLoop E C) (x : C) :
    ∃ V : Set C, IsOpen V ∧ x ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V,
      (∀ i s, (γ i).val s ≠ a) → (∀ i s, (γ i).val s ≠ b) →
      ∃ δ : ℝ → C, b3A_IsGoodPath (E := E) δ a b ∧ ∀ i s t, (γ i).val s = δ t →
        b3_orient E (b3_velocity E C (γ i).val s) (b3_velocity E C δ t) ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (chartAt E x).open_target _
    ((chartAt E x).map_source (mem_chart_source E x))
  let V := (chartAt E x).source ∩ chartAt E x ⁻¹' ball (chartAt E x x) r
  have hV : IsOpen V := (chartAt E x).continuousOn.isOpen_inter_preimage
    (chartAt E x).open_source isOpen_ball
  refine ⟨V, hV, ⟨mem_chart_source E x, mem_ball_self hr⟩, ?_⟩
  intro a ha b hb haoff hboff
  have heqa : (chartAt E x).symm (chartAt E x a) = a := (chartAt E x).left_inv ha.1
  have heqb : (chartAt E x).symm (chartAt E x b) = b := (chartAt E x).left_inv hb.1
  have he := exists_finitely_transverse_good_path_in_chart h γ x (chartAt E x a) (chartAt E x b)
    ha.2 hb.2 hball (by simpa only [heqa] using haoff) (by simpa only [heqb] using hboff)
  simpa only [heqa, heqb] using he

end HodgeLean.Foundations.Curves.AbelTheorem
