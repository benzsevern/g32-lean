import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineSpanExtension
import Mathlib.Tactic.Module

/-! An interior apex lies outside the affine span of every convex boundary piece. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_boundary_affineSpan {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C B : Set E) (hC : Convex ℝ C) (hB : Convex ℝ B) (hne : B.Nonempty)
    (hboundary : B ⊆ C \ intrinsicInterior ℝ C)
    (a : E) (ha : a ∈ intrinsicInterior ℝ C) : a ∉ affineSpan ℝ B := by
  intro haB
  obtain ⟨x, hx⟩ := hne.intrinsicInterior hB
  obtain ⟨t, ht, hy⟩ := s2v_hardt6rb_intrinsicInterior_extend_affineSpan B hx haB
  have hpos : 0 < 1 + t := by linarith
  have he : AffineMap.lineMap a (x + t • (x - a)) (1 / (1 + t)) = x := by
    have hv : x + t • (x - a) - a = (1 + t) • (x - a) := by module
    rw [AffineMap.lineMap_apply_module', hv, smul_smul, one_div,
      inv_mul_cancel₀ (ne_of_gt hpos), one_smul, sub_add_cancel]
  have hseg : x ∈ openSegment ℝ a (x + t • (x - a)) := by
    have hm := lineMap_mem_openSegment ℝ a (x + t • (x - a))
      (t := 1 / (1 + t)) ⟨by positivity, (div_lt_one hpos).mpr (by linarith)⟩
    rwa [he] at hm
  have hxC : x ∈ intrinsicInterior ℝ C :=
    hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior ha
      (subset_intrinsicClosure (hboundary hy).1) hseg
  exact (hboundary (intrinsicInterior_subset hx)).2 hxC

end HodgeLean.Foundations.Program
