import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenHullTopology

/-! Nonempty intrinsic simplex interiors are connected. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_interior_connected {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hs : s.Nonempty) :
    IsConnected (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) := by
  have hconv := convex_convexHull ℝ (↑s : Set E)
  have hopen : Convex ℝ (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) :=
    convex_iff_openSegment_subset.mpr fun x hx y hy =>
      hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        hx (subset_intrinsicClosure (intrinsicInterior_subset hy))
  have hnonempty : (convexHull ℝ (↑s : Set E)).Nonempty :=
    hs.to_set.mono (subset_convexHull ℝ (↑s : Set E))
  exact hopen.isConnected (hnonempty.intrinsicInterior hconv)

end HodgeLean.Foundations.Program
