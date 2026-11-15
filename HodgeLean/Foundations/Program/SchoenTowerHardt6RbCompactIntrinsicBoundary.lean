import Mathlib.Analysis.Convex.Intrinsic

/-! The actual intrinsic boundary of a finite-dimensional compact carrier is compact. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_intrinsic_boundary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : IsCompact C) : IsCompact (C \ intrinsicInterior ℝ C) := by
  have he : C \ intrinsicInterior ℝ C = intrinsicFrontier ℝ C := by
    rw [← closure_sdiff_intrinsicInterior, hC.isClosed.closure_eq]
  apply hC.of_isClosed_subset ?_ Set.diff_subset
  rw [he]
  exact isClosed_intrinsicFrontier (affineSpan ℝ C).closed_of_finiteDimensional

end HodgeLean.Foundations.Program
