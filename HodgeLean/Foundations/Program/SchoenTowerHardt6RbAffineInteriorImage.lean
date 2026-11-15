import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicExtension
import Mathlib.Tactic.Module

/-! Affine images of intrinsic interior points when the image carrier is convex. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_interior_image {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (S : Set E) (f : E →ᵃ[ℝ] F) (hC : Convex ℝ (f '' S))
    {x : E} (hx : x ∈ intrinsicInterior ℝ S) :
    f x ∈ intrinsicInterior ℝ (f '' S) := by
  have hne : (f '' S).Nonempty := ⟨f x, x, intrinsicInterior_subset hx, rfl⟩
  obtain ⟨v, hv⟩ := hne.intrinsicInterior hC
  obtain ⟨y, hy, rfl⟩ := intrinsicInterior_subset hv
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
  have hfseg : f x ∈ openSegment ℝ (f y) (f (x + t • (x - y))) := by
    rw [← image_openSegment ℝ f]
    exact ⟨x, hseg, rfl⟩
  exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hv
    (subset_intrinsicClosure ⟨_, hz, rfl⟩) hfseg

end HodgeLean.Foundations.Program
