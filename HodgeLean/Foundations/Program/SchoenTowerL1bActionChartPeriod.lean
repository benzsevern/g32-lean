import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Logic.Function.Iterate

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Each fixed finite iterate of a chart-conjugated map agrees near its
fixed point with the chart of the actual iterate. -/
theorem s2v_l1b_action_chart_iterates_eventually
    {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ)
    (x : M) (hx : x ∈ e.source) (f : M → M)
    (hf : ContinuousAt f x) (hfix : f x = x) (n : ℕ) :
    ∀ᶠ z : ℂ in 𝓝 (e x),
      (fun v => e (f (e.symm v)))^[n] z = e (f^[n] (e.symm z)) := by
  have hfixed (j : ℕ) : f^[j] x = x := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hsource (j : ℕ) : ∀ᶠ z : ℂ in 𝓝 (e x), f^[j] (e.symm z) ∈ e.source := by
    have hfc : ContinuousAt (f^[j]) (e.symm (e x)) := by
      rw [e.left_inv hx]
      exact hf.iterate hfix j
    have hc := hfc.comp (e.continuousAt_symm (e.map_source hx))
    have ht : Tendsto (fun z => f^[j] (e.symm z)) (𝓝 (e x)) (𝓝 x) := by
      simpa only [Function.comp_def, e.left_inv hx, hfixed] using hc.tendsto
    exact ht (e.open_source.mem_nhds hx)
  have htarget : ∀ᶠ z : ℂ in 𝓝 (e x), z ∈ e.target :=
    e.open_target.mem_nhds (e.map_source hx)
  induction n with
  | zero =>
    filter_upwards [htarget] with z hz
    simp only [Function.iterate_zero_apply, e.right_inv hz]
  | succ n ih =>
    filter_upwards [ih, hsource n] with z hz hzn
    rw [Function.iterate_succ_apply', hz]
    change e (f (e.symm (e (f^[n] (e.symm z))))) = e (f^[n + 1] (e.symm z))
    rw [e.left_inv hzn, Function.iterate_succ_apply']

/-- A finite period of the actual action gives the same local period in
any chart at its fixed point. -/
theorem s2v_l1b_action_chart_period_eventually
    {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ)
    (x : M) (hx : x ∈ e.source) (f : M → M)
    (hf : ContinuousAt f x) (hfix : f x = x) (N : ℕ)
    (hperiod : ∀ y, f^[N] y = y) :
    ∀ᶠ z : ℂ in 𝓝 (e x), (fun v => e (f (e.symm v)))^[N] z = z := by
  have hi := s2v_l1b_action_chart_iterates_eventually e x hx f hf hfix N
  have ht : ∀ᶠ z : ℂ in 𝓝 (e x), z ∈ e.target :=
    e.open_target.mem_nhds (e.map_source hx)
  filter_upwards [hi, ht] with z hz hzt
  rw [hz, hperiod, e.right_inv hzt]

/-- Centering a fixed-point chart preserves the local period of the actual
action. -/
theorem s2v_l1b_action_centered_chart_period_eventually
    {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ)
    (x : M) (hx : x ∈ e.source) (f : M → M)
    (hf : ContinuousAt f x) (hfix : f x = x) (N : ℕ)
    (hperiod : ∀ y, f^[N] y = y) :
    ∀ᶠ z : ℂ in 𝓝 0,
      (fun v => e (f (e.symm (v + e x))) - e x)^[N] z = z := by
  let R : ℂ → ℂ := fun v => e (f (e.symm v))
  let C : ℂ → ℂ := fun v => R (v + e x) - e x
  have hshift (n : ℕ) (z : ℂ) : C^[n] z = R^[n] (z + e x) - e x := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, add_sub_cancel_right]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      dsimp only [C]
      rw [sub_add_cancel, Function.iterate_succ_apply']
  have hi := s2v_l1b_action_chart_period_eventually e x hx f hf hfix N hperiod
  have ht : Tendsto (fun z : ℂ => z + e x) (𝓝 0) (𝓝 (e x)) := by
    have hcont : Continuous (fun z : ℂ => z + e x) := continuous_id.add continuous_const
    simpa only [zero_add] using hcont.tendsto (0 : ℂ)
  filter_upwards [ht.eventually hi] with z hz
  change C^[N] z = z
  rw [hshift, hz, add_sub_cancel_right]

end HodgeLean.Foundations.Program
