import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Topology

/-! Every convex carrier point is approximated by its intrinsic interior. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_convex_subset_closure_intrinsicInterior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) : C ⊆ closure (intrinsicInterior ℝ C) := by
  intro y hy
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hC ⟨y, hy⟩
  apply closure_mono (hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
    hx (subset_intrinsicClosure hy))
  exact segment_subset_closure_openSegment (right_mem_segment ℝ x y)

end HodgeLean.Foundations.Program
