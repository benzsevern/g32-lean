import HodgeLean.Adapters.NormalConeB4aClassRemovable
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmert
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Continuous extension across thin analytic sets

Route: local defining equations and density of the complement provide one
nonzero analytic germ. On a small connected ball its zero set contains the
exceptional set. Continuous extension across that hypersurface applies.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open HodgeLean.Foundations.Analytic

/-- A continuous function analytic away from a locally analytic subset with
dense complement is analytic on its whole open domain. -/
theorem a3b4a_classAnalytic_extend_across_set
    (d : ℕ) (V A : Set (Fin (d+1) → ℂ)) (hV : IsOpen V)
    (hA : ∀ x ∈ V ∩ A, anrem_LocEq A x) (hdense : V ⊆ closure (V \ A))
    (f : (Fin (d+1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f (V \ A))
    (hcont : ContinuousOn f V) : AnalyticOnNhd ℂ f V := by
  intro x hx
  by_cases hxA : x ∈ A
  · obtain ⟨U, hU, hxU, k, g, hg, hEq⟩ := hA x ⟨hx, hxA⟩
    have hj : ∃ j, ¬ (g j =ᶠ[𝓝 x] fun _ => 0) := by
      by_contra h
      push_neg at h
      have hall : ∀ᶠ y in 𝓝 x, ∀ j, g j y = 0 := Filter.eventually_all.mpr h
      have hfreq : ∃ᶠ y in 𝓝 x, y ∈ V \ A := mem_closure_iff_frequently.mp (hdense hx)
      obtain ⟨y, hy, hyall, hyU⟩ :=
        (hfreq.and_eventually (hall.and (hU.mem_nhds hxU))).exists
      exact hy.2 ((hEq y hyU).mpr hyall)
    obtain ⟨j, hj⟩ := hj
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      ((hU.inter hV).mem_nhds ⟨hxU, hx⟩)
    have hBU : Metric.ball x r ⊆ U := fun y hy => (hball hy).1
    have hBV : Metric.ball x r ⊆ V := fun y hy => (hball hy).2
    have hnz : ∀ y ∈ Metric.ball x r, ¬ (g j =ᶠ[𝓝 y] fun _ => 0) := by
      intro y hy hz
      apply hj
      have he := (hg j |>.mono hBU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball x r).isPreconnected hy hz
      filter_upwards [Metric.ball_mem_nhds x hr] with z hzB
      exact he hzB
    have hfa : AnalyticOnNhd ℂ f (Metric.ball x r \ {y | g j y = 0}) := by
      intro y hy
      apply hf y
      refine ⟨hBV hy.1, ?_⟩
      intro hyA
      exact hy.2 ((hEq y (hBU hy.1)).mp hyA j)
    exact a3b4a_classAnalytic_extend_continuous d (Metric.ball x r) Metric.isOpen_ball
      (g j) f ((hg j).mono hBU) hnz hfa (hcont.mono hBV) x (Metric.mem_ball_self hr)
  · exact hf x ⟨hx, hxA⟩

end HodgeLean.Adapters
