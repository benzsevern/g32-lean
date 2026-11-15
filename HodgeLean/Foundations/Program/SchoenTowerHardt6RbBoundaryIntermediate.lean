import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Linarith

/-! Every intermediate height between two boundary graph limits is another boundary graph limit. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_boundary_graph_intermediate {E : Type*} [MetricSpace E]
    (C : Set E) (f : E → ℝ) (hf : ContinuousOn f C) (a : E)
    (hlocal : ∀ ε : ℝ, 0 < ε → IsPreconnected (C ∩ Metric.ball a ε))
    {y z w : ℝ}
    (hy : (a, y) ∈ closure ((fun x => (x, f x)) '' C))
    (hz : (a, z) ∈ closure ((fun x => (x, f x)) '' C))
    (hyw : y < w) (hwz : w < z) :
    (a, w) ∈ closure ((fun x => (x, f x)) '' C) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p, hp, hpy⟩ := Metric.mem_closure_iff.mp hy (min ε (w - y))
    (lt_min hε (sub_pos.mpr hyw))
  obtain ⟨x, hxC, rfl⟩ := hp
  obtain ⟨q, hq, hqz⟩ := Metric.mem_closure_iff.mp hz (min ε (z - w))
    (lt_min hε (sub_pos.mpr hwz))
  obtain ⟨v, hvC, rfl⟩ := hq
  rw [Prod.dist_eq] at hpy hqz
  have hxnear : dist x a < ε := by
    rw [dist_comm]
    exact lt_of_lt_of_le (max_lt_iff.mp hpy).1 (min_le_left _ _)
  have hvnear : dist v a < ε := by
    rw [dist_comm]
    exact lt_of_lt_of_le (max_lt_iff.mp hqz).1 (min_le_left _ _)
  have hxlow : f x < w := by
    have h := lt_of_lt_of_le (max_lt_iff.mp hpy).2 (min_le_right _ _)
    rw [Real.dist_eq] at h
    have hh := (abs_lt.mp h).1
    linarith
  have hvhigh : w < f v := by
    have h := lt_of_lt_of_le (max_lt_iff.mp hqz).2 (min_le_right _ _)
    rw [Real.dist_eq] at h
    have hh := (abs_lt.mp h).2
    linarith
  obtain ⟨u, hu, hfu⟩ := (hlocal ε hε).intermediate_value ⟨hxC, hxnear⟩ ⟨hvC, hvnear⟩
    (hf.mono Set.inter_subset_left) ⟨hxlow.le, hvhigh.le⟩
  refine ⟨(u, f u), ⟨u, hu.1, rfl⟩, ?_⟩
  rw [Prod.dist_eq, hfu, dist_self]
  exact max_lt_iff.mpr ⟨by simpa only [Metric.mem_ball, dist_comm] using hu.2, hε⟩

end HodgeLean.Foundations.Program
