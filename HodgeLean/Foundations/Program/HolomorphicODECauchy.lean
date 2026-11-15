import HodgeLean.Foundations.Program.HolomorphicODEIntegral

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

theorem b65_norm_fderiv_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {x : E} {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall x δ))
    (hb : ∀ y ∈ closedBall x δ, ‖f y‖ ≤ M) :
    ‖fderiv ℂ f x‖ ≤ M / δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM hδ.le)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r := δ / ‖v‖
  have hr : 0 < r := div_pos hδ hvn
  have hm : ∀ t ∈ closedBall (0 : ℂ) r, x + t • v ∈ closedBall x δ := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have ht' : ‖t‖ ≤ δ / ‖v‖ := by simpa [r] using ht
    exact (le_div_iff₀ hvn).mp ht'
  have ha : AnalyticOnNhd ℂ (fun t : ℂ ↦ f (x + t • v)) (closedBall 0 r) := by
    intro t ht
    apply (hf _ (hm t ht)).comp (f := fun t : ℂ ↦ x + t • v)
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ x) t).add
      ((analyticAt_id : AnalyticAt ℂ (fun t : ℂ ↦ t) t).smul analyticAt_const)
  have hd : HasDerivAt (fun t : ℂ ↦ f (x + t • v)) (fderiv ℂ f x v) 0 := by
    have hx : x ∈ closedBall x δ := mem_closedBall_self hδ.le
    have hh : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
      simpa using (hf x hx).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun t : ℂ ↦ x + t • v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x)
    simpa [Function.comp_def] using hh.comp_hasDerivAt 0 hl
  have hc : DiffContOnCl ℂ (fun t : ℂ ↦ f (x + t • v)) (ball 0 r) := by
    refine ⟨ha.differentiableOn.mono ball_subset_closedBall, ?_⟩
    simpa [closure_ball _ hr.ne'] using ha.continuousOn
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hc
    (fun t ht ↦ hb _ (hm t (sphere_subset_closedBall ht)))
  rw [hd.deriv] at hh
  calc
    ‖(fderiv ℂ f x) v‖ ≤ M / r := hh
    _ = M / δ * ‖v‖ := by dsimp [r]; field_simp

theorem b65_state_fderiv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {c : E} {S M : ℝ}
    (hS : 0 < S) (hM : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball c S))
    (hb : ∀ v ∈ ball c S, ‖f v‖ ≤ M) {x : E} (hx : x ∈ ball c (3 * S / 4)) :
    ‖fderiv ℂ f x‖ ≤ 4 * M / S := by
  have hd : 0 < S / 4 := by positivity
  have hs : closedBall x (S / 4) ⊆ ball c S := by
    intro v hv
    rw [mem_ball]
    have ht := dist_triangle v x c
    have hv' := mem_closedBall.mp hv
    have hx' := mem_ball.mp hx
    linarith
  have hh := b65_norm_fderiv_le hd hM (hf.mono hs) (fun v hv ↦ hb v (hs hv))
  convert hh using 1 <;> ring

theorem b65_state_lipschitz_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {c : E} {S M : ℝ}
    (hS : 0 < S) (hM : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball c S))
    (hb : ∀ v ∈ ball c S, ‖f v‖ ≤ M) {x y : E}
    (hx : x ∈ ball c (3 * S / 4)) (hy : y ∈ ball c (3 * S / 4)) :
    ‖f x - f y‖ ≤ (4 * M / S) * ‖x - y‖ := by
  have hs : ball c (3 * S / 4) ⊆ ball c S := ball_subset_ball (by linarith)
  exact (convex_ball c (3 * S / 4)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v hv ↦ (hf v (hs hv)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (fun v hv ↦ b65_state_fderiv_bound hS hM hf hb hv) hy hx

end HodgeLean.Foundations.Program
