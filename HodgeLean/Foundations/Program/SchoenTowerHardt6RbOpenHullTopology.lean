import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicDensity

/-! Intrinsic finite-hull interiors have their exact compact closures and connected local neighborhoods. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_open_hull_topology {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) :
    closure (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) = convexHull ℝ (↑s : Set E) ∧
      ∀ a : E, ∀ ε : ℝ,
        IsPreconnected (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)) ∩ Metric.ball a ε) := by
  have hconv : Convex ℝ (convexHull ℝ (↑s : Set E)) := convex_convexHull ℝ _
  have hclosed : IsClosed (convexHull ℝ (↑s : Set E)) := s.finite_toSet.isCompact_convexHull ℝ |>.isClosed
  have hopen : Convex ℝ (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) :=
    convex_iff_openSegment_subset.mpr fun x hx y hy =>
      hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        hx (subset_intrinsicClosure (intrinsicInterior_subset hy))
  refine ⟨Set.Subset.antisymm (closure_minimal intrinsicInterior_subset hclosed)
    (s2v_hardt6rb_convex_subset_closure_intrinsicInterior _ hconv), ?_⟩
  intro a ε
  exact (hopen.inter (convex_ball a ε)).isPreconnected

end HodgeLean.Foundations.Program
