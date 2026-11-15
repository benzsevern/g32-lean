import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryIntermediate
import Mathlib.Topology.Separation.Connected

/-! Finite boundary graph fibers over locally connected bases have at most one height. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_finite_boundary_fiber_unique {E : Type*} [MetricSpace E]
    (C : Set E) (f : E → ℝ) (hf : ContinuousOn f C) (a : E)
    (hlocal : ∀ ε : ℝ, 0 < ε → IsPreconnected (C ∩ Metric.ball a ε))
    (hfinite : Set.Finite {t : ℝ | (a, t) ∈ closure ((fun x => (x, f x)) '' C)}) :
    Set.Subsingleton {t : ℝ | (a, t) ∈ closure ((fun x => (x, f x)) '' C)} := by
  have hpre : IsPreconnected {t : ℝ | (a, t) ∈ closure ((fun x => (x, f x)) '' C)} := by
    apply Set.OrdConnected.isPreconnected
    constructor
    intro y hy z hz w hw
    by_cases hwy : w = y
    · exact hwy.symm ▸ hy
    by_cases hwz : w = z
    · exact hwz.symm ▸ hz
    exact s2v_hardt6rb_boundary_graph_intermediate C f hf a hlocal hy hz
      (lt_of_le_of_ne hw.1 (Ne.symm hwy)) (lt_of_le_of_ne hw.2 hwz)
  by_contra hn
  exact hfinite.not_infinite (hpre.infinite_of_nontrivial (Set.not_subsingleton_iff.mp hn))

end HodgeLean.Foundations.Program
