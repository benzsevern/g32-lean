import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicPositive
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPositiveIntrinsic

/-! Exact positive-coordinate description of an independent simplex's intrinsic open face. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_intrinsicInterior_iff {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) (x : E) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range v)) ↔
      ∃ w : stdSimplex ℝ ι, (∀ i, 0 < w.val i) ∧ (∑ i, w.val i • v i) = x := by
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights v x).mp (intrinsicInterior_subset hx)
    have hpos := s2v_hardt6rb_intrinsicInterior_weights_pos v hv w (hw.symm ▸ hx)
    exact ⟨w, hpos, hw⟩
  · rintro ⟨w, hpos, rfl⟩
    exact s2v_hardt6rb_positive_weights_mem_intrinsicInterior v w hpos

end HodgeLean.Foundations.Program
