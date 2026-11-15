import HodgeLean.Foundations.Program.HolomorphicODELinearSeries

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

theorem b65_uniform_clm_apply {X E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set X} {f : ℕ → X → E} {g : X → E} {A : X → E →L[ℂ] F} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ x ∈ U, ‖A x‖ ≤ C) (hg : TendstoUniformlyOn f g atTop U) :
    TendstoUniformlyOn (fun n x ↦ A x (f n x)) (fun x ↦ A x (g x)) atTop U := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hC' : 0 < C + 1 := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hg (ε / (C + 1)) (div_pos hε hC')] with n hn x hx
  calc
    dist (A x (g x)) (A x (f n x)) = ‖A x (g x - f n x)‖ := by rw [dist_eq_norm, map_sub]
    _ ≤ ‖A x‖ * ‖g x - f n x‖ := (A x).le_opNorm _
    _ ≤ (C + 1) * dist (g x) (f n x) := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right ((hA x hx).trans (by linarith)) (norm_nonneg _)
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left (hn x hx) hC'
    _ = ε := by field_simp

end HodgeLean.Foundations.Program
