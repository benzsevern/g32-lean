import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenHullTopology

/-! Intrinsic simplex interiors are dense in their actual carrier subtypes. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_interior_dense {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) :
    DenseRange (Set.inclusion (intrinsicInterior_subset (𝕜 := ℝ)
      (s := convexHull ℝ (↑s : Set E)))) := by
  rw [denseRange_inclusion_iff, (s2v_hardt6rb_open_hull_topology s).1]

end HodgeLean.Foundations.Program
