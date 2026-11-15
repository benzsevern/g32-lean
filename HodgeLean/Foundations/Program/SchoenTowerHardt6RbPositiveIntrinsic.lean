import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPositiveWeightsSplit
import Mathlib.Analysis.Convex.Intrinsic

/-! Strictly positive convex coordinates lie in the intrinsic interior of their finite hull. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_positive_weights_mem_intrinsicInterior {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (v : ι → E) (w : stdSimplex ℝ ι) (hw : ∀ i, 0 < w.val i) :
    (∑ i, w.val i • v i) ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range v)) := by
  have hx : (∑ i, w.val i • v i) ∈ convexHull ℝ (Set.range v) :=
    (s2v_hardt6rb_convexHull_range_weights v _).mpr ⟨w, rfl⟩
  obtain ⟨y, hy⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (Set.range v)) ⟨_, hx⟩
  have hyHull : y ∈ convexHull ℝ (Set.range v) := intrinsicInterior_subset hy
  obtain ⟨u, hu⟩ := (s2v_hardt6rb_convexHull_range_weights v y).mp hyHull
  obtain ⟨t, ht, z, hz⟩ := s2v_hardt6rb_positive_weights_split w u hw
  have hzHull : (∑ i, z.val i • v i) ∈ convexHull ℝ (Set.range v) :=
    (s2v_hardt6rb_convexHull_range_weights v _).mpr ⟨z, rfl⟩
  have he : t • y + (1 - t) • (∑ i, z.val i • v i) = ∑ i, w.val i • v i := by
    rw [← hu]
    simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun r : ℝ => r • v i) (hz i).symm
  apply (convex_convexHull ℝ (Set.range v)).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
    hy (subset_intrinsicClosure hzHull)
  exact ⟨t, 1 - t, ht.1, sub_pos.mpr ht.2, by linarith, he⟩

end HodgeLean.Foundations.Program
