import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Positive rays from an intrinsic interior apex meet a convex boundary in at most one point. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_boundary_ray_unique {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Convex ℝ C) (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    {x y : E} (hx : x ∈ C \ intrinsicInterior ℝ C)
    (hy : y ∈ C \ intrinsicInterior ℝ C) {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (he : AffineMap.lineMap a x t = AffineMap.lineMap a y u) : t = u ∧ x = y := by
  have hle : ∀ {x y : E} {t u : ℝ}, x ∈ C → y ∈ C \ intrinsicInterior ℝ C →
      0 < t → 0 < u → AffineMap.lineMap a x t = AffineMap.lineMap a y u → u ≤ t := by
    intro x y t u hx hy ht hu he
    by_contra hn
    have htu : t < u := lt_of_not_ge hn
    have hy' : AffineMap.lineMap a x (t / u) = y := by
      calc
        AffineMap.lineMap a x (t / u) =
            AffineMap.lineMap a (AffineMap.lineMap a x t) (1 / u) := by
          rw [AffineMap.lineMap_lineMap_right]
          congr 1
          ring
        _ = AffineMap.lineMap a (AffineMap.lineMap a y u) (1 / u) := by rw [he]
        _ = y := by simp [AffineMap.lineMap_lineMap_right, ne_of_gt hu]
    have hm := lineMap_mem_openSegment ℝ a x (t := t / u)
      ⟨div_pos ht hu, (div_lt_one hu).mpr htu⟩
    rw [hy'] at hm
    exact hy.2 (hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      ha (subset_intrinsicClosure hx) hm)
  have htu : t = u := le_antisymm (hle hy.1 hx hu ht he.symm) (hle hx.1 hy ht hu he)
  refine ⟨htu, ?_⟩
  subst u
  have hh := congrArg (fun z => AffineMap.lineMap a z (1 / t)) he
  simpa [AffineMap.lineMap_lineMap_right, ne_of_gt ht] using hh

end HodgeLean.Foundations.Program
