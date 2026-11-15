import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Compact

/-! Bounded graph closures over compact base closures cover the entire base closure. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_bounded_graph_closure {E : Type*} [MetricSpace E]
    (C : Set E) (hC : IsCompact (closure C)) (f : E → ℝ) (l u : ℝ)
    (hbound : ∀ x ∈ C, f x ∈ Set.Icc l u) :
    IsCompact (closure ((fun x => (x, f x)) '' C)) ∧
      Prod.fst '' closure ((fun x => (x, f x)) '' C) = closure C := by
  have hsub : closure ((fun x => (x, f x)) '' C) ⊆ closure C ×ˢ Set.Icc l u := by
    apply closure_minimal ?_ (hC.isClosed.prod isClosed_Icc)
    rintro p ⟨x, hx, rfl⟩
    exact ⟨subset_closure hx, hbound x hx⟩
  have hcompact : IsCompact (closure ((fun x => (x, f x)) '' C)) :=
    (hC.prod isCompact_Icc).of_isClosed_subset isClosed_closure hsub
  refine ⟨hcompact, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨p, hp, rfl⟩
    exact (hsub hp).1
  · apply closure_minimal ?_ (hcompact.image continuous_fst).isClosed
    intro x hx
    exact ⟨(x, f x), subset_closure ⟨x, hx, rfl⟩, rfl⟩

end HodgeLean.Foundations.Program
