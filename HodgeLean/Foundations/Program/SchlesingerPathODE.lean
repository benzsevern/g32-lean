import HodgeLean.Foundations.Program.SchlesingerPathDefs
import HodgeLean.Foundations.Program.HolomorphicODE
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_local_ode (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (F : ℂ × E → E) (y₀ : E)
    (hF : AnalyticAt ℂ F (0, y₀)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ y : ℂ → E,
      AnalyticOnNhd ℂ y (ball 0 ρ) ∧ y 0 = y₀ ∧
      ∀ z ∈ ball (0 : ℂ) ρ, HasDerivAt y (F (z, y z)) z := by
  have hb : ∀ᶠ q in 𝓝 (0, y₀), ‖F q‖ < ‖F (0, y₀)‖ + 1 :=
    hF.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (hF.eventually_analyticAt.and hb)
  have hsub : ball (0 : ℂ) ε ×ˢ ball y₀ ε ⊆ ball (0, y₀) ε := by
    intro q hq
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using
      (show dist q.1 0 < ε ∧ dist q.2 y₀ < ε from hq)
  have hM : 0 ≤ ‖F (0, y₀)‖ + 1 := by positivity
  obtain ⟨y, hy, hy₀, _, hdy⟩ := b65_holomorphic_ode E F 0 y₀ ε ε
    (‖F (0, y₀)‖ + 1) hε hε hM
    (fun q hq ↦ (he (hsub hq)).1) (fun q hq ↦ (he (hsub hq)).2.le)
  exact ⟨_, by dsimp [b65_radius]; positivity, y, hy, hy₀, hdy⟩

theorem b65p_ode_unique (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (F : ℂ × E → E) (y₀ : E)
    (hF : AnalyticAt ℂ F (0, y₀)) (r : ℝ) (hr : 0 < r)
    (y z : ℂ → E) (hy₀ : y 0 = y₀) (hz₀ : z 0 = y₀)
    (hy : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt y (F (x, y x)) x)
    (hz : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt z (F (x, z x)) x) :
    EqOn y z (ball (0 : ℂ) r) := by
  obtain ⟨ε, hε, he⟩ := hF.exists_ball_analyticOnNhd
  have hym : ∀ᶠ x in 𝓝 (0 : ℂ), y x ∈ ball y₀ ε := by
    have h := (hy 0 (mem_ball_self hr)).continuousAt
    have h' : Tendsto y (𝓝 0) (𝓝 y₀) := by simpa only [hy₀] using h.tendsto
    exact h'.eventually (ball_mem_nhds y₀ hε)
  have hzm : ∀ᶠ x in 𝓝 (0 : ℂ), z x ∈ ball y₀ ε := by
    have h := (hz 0 (mem_ball_self hr)).continuousAt
    have h' : Tendsto z (𝓝 0) (𝓝 y₀) := by simpa only [hz₀] using h.tendsto
    exact h'.eventually (ball_mem_nhds y₀ hε)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (hym.and hzm)
  let τ := min r (min ε δ)
  have hτ : 0 < τ := lt_min hr (lt_min hε hδ)
  have hτr : τ ≤ r := min_le_left _ _
  have hτε : τ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hτδ : τ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hlocal := b65_holomorphic_ode_unique E F 0 y₀ τ ε hτ hε
    (he.mono (by
      intro q hq
      simp only [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨lt_of_lt_of_le (mem_ball.mp hq.1) hτε, mem_ball.mp hq.2⟩))
    y z hy₀ hz₀ (fun x hx ↦ (hd (ball_subset_ball hτδ hx)).1)
      (fun x hx ↦ (hd (ball_subset_ball hτδ hx)).2)
      (fun x hx ↦ hy x (ball_subset_ball hτr hx))
      (fun x hx ↦ hz x (ball_subset_ball hτr hx))
  have hya : AnalyticOnNhd ℂ y (ball (0 : ℂ) r) :=
    (show DifferentiableOn ℂ y (ball (0 : ℂ) r) from
      fun x hx ↦ (hy x hx).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have hza : AnalyticOnNhd ℂ z (ball (0 : ℂ) r) :=
    (show DifferentiableOn ℂ z (ball (0 : ℂ) r) from
      fun x hx ↦ (hz x hx).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  exact hya.eqOn_of_preconnected_of_eventuallyEq hza (convex_ball (0 : ℂ) r).isPreconnected
    (mem_ball_self hr) (Filter.eventually_of_mem (ball_mem_nhds 0 hτ) (fun x hx ↦ hlocal hx))

theorem b65p_field_analytic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℂ → ι → ℂ) (r : ℝ)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun z ↦ t z q) (ball 0 r))
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) (hinj : Function.Injective (t z))
    (A : ι → E →L[ℂ] E) :
    AnalyticAt ℂ (fun w : ℂ × (ι → E →L[ℂ] E) ↦
      b65p_schlesingerField E (fun q ↦ deriv (fun z ↦ t z q) w.1) (t w.1) w.2) (z, A) := by
  apply analyticAt_pi_iff.mpr
  intro p
  unfold b65p_schlesingerField
  apply Finset.analyticAt_fun_sum
  intro q _
  by_cases h : q = p
  · simp only [h, ite_true]
    exact analyticAt_const
  · simp only [if_neg h]
    have htp := (ht p z hz).comp (x := (z, A)) analyticAt_fst
    have htq := (ht q z hz).comp (x := (z, A)) analyticAt_fst
    have hvp := (ht p z hz).deriv.comp (x := (z, A)) analyticAt_fst
    have hvq := (ht q z hz).deriv.comp (x := (z, A)) analyticAt_fst
    have hAp : AnalyticAt ℂ (fun w : ℂ × (ι → E →L[ℂ] E) ↦ w.2 p) (z, A) := by
      exact ((ContinuousLinearMap.proj p : (ι → E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)).analyticAt A).comp (x := (z, A)) analyticAt_snd
    have hAq : AnalyticAt ℂ (fun w : ℂ × (ι → E →L[ℂ] E) ↦ w.2 q) (z, A) := by
      exact ((ContinuousLinearMap.proj q : (ι → E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)).analyticAt A).comp (x := (z, A)) analyticAt_snd
    exact ((hvp.sub hvq).div (htp.sub htq) (sub_ne_zero.mpr (fun h' ↦ h (hinj h').symm))).smul
      ((hAq.mul hAp).sub (hAp.mul hAq))

end HodgeLean.Foundations.Program
