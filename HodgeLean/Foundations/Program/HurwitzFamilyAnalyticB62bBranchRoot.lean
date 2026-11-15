import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bTransitions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Filter
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

theorem b6a_analyticAt_root_monomial (r : ℂ → ℂ) (e m : ℕ) (he : 0 < e)
    (hr : ∀ᶠ z in 𝓝 (0 : ℂ), ContinuousAt r z)
    (hpow : ∀ᶠ z in 𝓝 (0 : ℂ), r z ^ e = z ^ m) : AnalyticAt ℂ r 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hloc := eventually_eventually_nhds.mpr hpow
    filter_upwards [hr.filter_mono nhdsWithin_le_nhds,
      hloc.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hrc hp hz
    have hne : r z ≠ 0 := by
      intro hzero
      have hpz : r z ^ e = z ^ m :=
        Filter.Eventually.self_of_nhds (p := fun w ↦ r w ^ e = w ^ m) hp
      rw [hzero, zero_pow he.ne'] at hpz
      exact pow_ne_zero m hz hpz.symm
    have hh : ContDiffAt ℂ ω (fun y ↦ r y ^ e) z :=
      (contDiffAt_id.pow m).congr_of_eventuallyEq hp
    exact (b6a_contDiffAt_of_pow r z e he hrc hne hh).differentiableAt (by simp)
  · exact Filter.Eventually.self_of_nhds hr

theorem b6a_constant_of_pow_eq {E : Type} [TopologicalSpace E]
    (s : Set E) (hs : IsPreconnected s) (r : E → ℂ)
    (hr : ContinuousOn r s) (e : ℕ) (he : 0 < e) (c : ℂ)
    (hp : ∀ x ∈ s, r x ^ e = c) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    r x = r y := by
  have hf : Set.Finite {z : ℂ | z ^ e = c} := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using
      (Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero he c))
  exact hs.constant_of_mapsTo hf.isDiscrete hr hp hx hy

theorem b6a_contDiffAt_root_product_monomial {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : E × ℂ → ℂ) (a : E) (e m : ℕ) (he : 0 < e)
    (hr : ∀ᶠ z in 𝓝 (a, (0 : ℂ)), ContinuousAt r z)
    (hp : ∀ᶠ z in 𝓝 (a, (0 : ℂ)), r z ^ e = z.2 ^ m) :
    ContDiffAt ℂ ω r (a, (0 : ℂ)) := by
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hr.and hp)
  have hprod (t : E) (z : ℂ) (ht : t ∈ Metric.ball a R)
      (hz : z ∈ Metric.ball (0 : ℂ) R) :
      ContinuousAt r (t, z) ∧ r (t, z) ^ e = z ^ m :=
    hball (t, z) (by simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using And.intro ht hz)
  have ha : a ∈ Metric.ball a R := Metric.mem_ball_self hR
  have hslice : AnalyticAt ℂ (fun z ↦ r (a, z)) 0 := by
    apply b6a_analyticAt_root_monomial _ e m he
    · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
      exact (hprod a z ha hz).1.comp (continuous_const.prodMk continuous_id).continuousAt
    · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
      exact (hprod a z ha hz).2
  apply (hslice.contDiffAt.comp (a, (0 : ℂ)) contDiffAt_snd).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (a, (0 : ℂ)) hR] with q hq
  have hq : q.1 ∈ Metric.ball a R ∧ q.2 ∈ Metric.ball (0 : ℂ) R := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using hq
  exact b6a_constant_of_pow_eq (Metric.ball a R) Metric.isPreconnected_ball
    (fun t ↦ r (t, q.2))
    (fun t ht ↦ ((hprod t q.2 ht hq.2).1.comp (f := fun u : E ↦ (u, q.2))
      (continuous_id.prodMk continuous_const).continuousAt).continuousWithinAt)
    e he (q.2 ^ m) (fun t ht ↦ (hprod t q.2 ht hq.2).2) hq.1 ha

end HodgeLean.Foundations.Program
