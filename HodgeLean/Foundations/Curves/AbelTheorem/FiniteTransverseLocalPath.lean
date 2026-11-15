import HodgeLean.Foundations.Curves.AbelTheorem.FiniteGenericPoint
import HodgeLean.Foundations.Curves.AbelTheorem.TransverseChartSegment
import HodgeLean.Foundations.Curves.AbelTheorem.TransverseConcat

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

theorem exists_finitely_transverse_good_path_in_chart (h : Module.finrank ℂ E = 1)
    {ι : Type} [Fintype ι] (γ : ι → b3_SmoothLoop E C)
    (x : C) (a b : E) {r : ℝ}
    (ha : a ∈ ball (chartAt E x x) r) (hb : b ∈ ball (chartAt E x x) r)
    (hball : ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (henda : ∀ i s, (γ i).val s ≠ (chartAt E x).symm a)
    (hendb : ∀ i s, (γ i).val s ≠ (chartAt E x).symm b) :
    ∃ δ : ℝ → C, b3A_IsGoodPath (E := E) δ ((chartAt E x).symm a) ((chartAt E x).symm b) ∧
      ∀ i s t, (γ i).val s = δ t →
        b3_orient E (b3_velocity E C (γ i).val s) (b3_velocity E C δ t) ≠ 0 := by
  obtain ⟨v, hv, hgen⟩ := exists_generic_point_for_finite_paths h (fun i => (γ i).val)
    (fun i => (γ i).property.2) x a b isOpen_ball ⟨a, ha⟩
  have hvT := hball hv
  have hoff : ∀ i s, (γ i).val s ≠ (chartAt E x).symm v := by
    intro i s hs
    apply (hgen i).1
    refine ⟨s, ?_, ?_⟩
    · rw [hs]
      exact (chartAt E x).map_target hvT
    · rw [hs, (chartAt E x).right_inv hvT]
  have hgooda := b3A_isGoodPath_segment x a v (((convex_ball _ _).segment_subset ha hv).trans hball)
  have hgoodb := b3A_isGoodPath_segment x b v (((convex_ball _ _).segment_subset hb hv).trans hball)
  have hatr i := chart_segment_transverse_of_not_bad h (γ i) x a v ha hv hball
    (henda i) (hoff i) (hgen i).2.1
  have hbtr i := chart_segment_transverse_of_not_bad h (γ i) x b v hb hv hball
    (hendb i) (hoff i) (hgen i).2.2
  let ε : ℝ → C := fun t => b3Forms_segPath x b v (1 - t)
  have hε : b3A_IsGoodPath (E := E) ε ((chartAt E x).symm v) ((chartAt E x).symm b) := hgoodb.symm
  have hεtr i : ∀ s t, (γ i).val s = ε t →
      b3_orient E (b3_velocity E C (γ i).val s) (b3_velocity E C ε t) ≠ 0 := by
    apply transverse_path_reparam (γ i) _ hgoodb.1 (hbtr i) (fun t : ℝ => 1 - t)
      (contDiff_const.sub contDiff_id)
    intro s t _
    have hd : deriv (fun u : ℝ => 1 - u) t = -1 := by
      simpa using ((hasDerivAt_id t).const_sub 1).deriv
    rw [hd]
    norm_num
  exact ⟨_, hgooda.trans hε, fun i =>
    transverse_path_concat (γ i) _ ε hgooda.1 hε.1 (hatr i) (hεtr i) _ hgooda.apply_one (hoff i)⟩

end HodgeLean.Foundations.Curves.AbelTheorem
