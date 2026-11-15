import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineInteriorImage

/-! Intrinsic interiors of subsets meeting the intrinsic interior of a convex carrier. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_intrinsicInterior_subset_of_meets {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S C : Set E} (hSC : S ⊆ C) (hC : Convex ℝ C)
    (hmeet : ∃ y ∈ S, y ∈ intrinsicInterior ℝ C) :
    intrinsicInterior ℝ S ⊆ intrinsicInterior ℝ C := by
  rintro x hx
  obtain ⟨y, hy, hyC⟩ := hmeet
  obtain ⟨t, ht, hz⟩ := s2v_hardt6rb_intrinsicInterior_extend S hx hy
  have hpos : 0 < 1 + t := by linarith
  have he : AffineMap.lineMap y (x + t • (x - y)) (1 / (1 + t)) = x := by
    have hh : x + t • (x - y) - y = (1 + t) • (x - y) := by module
    rw [AffineMap.lineMap_apply_module', hh, smul_smul, one_div,
      inv_mul_cancel₀ (ne_of_gt hpos), one_smul, sub_add_cancel]
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    have hh := lineMap_mem_openSegment ℝ y (x + t • (x - y))
      (t := 1 / (1 + t)) ⟨by positivity, (div_lt_one hpos).mpr (by linarith)⟩
    rwa [he] at hh
  exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hyC
    (subset_intrinsicClosure (hSC hz)) hseg

end HodgeLean.Foundations.Program
