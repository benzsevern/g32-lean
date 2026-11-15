import Mathlib.Analysis.Convex.Join
import Mathlib.Data.Real.Basic

/-! Actual coordinates on the convex hull of an apex and a nonempty finite base. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_coordinates {E : Type*} [DecidableEq E] [AddCommGroup E] [Module ℝ E]
    (a : E) (s : Finset E) (hs : s.Nonempty) (x : E) :
    x ∈ convexHull ℝ (↑(insert a s) : Set E) ↔
      ∃ y ∈ convexHull ℝ (↑s : Set E), ∃ t ∈ Set.Icc (0 : ℝ) 1,
        AffineMap.lineMap a y t = x := by
  classical
  rw [Finset.coe_insert, convexHull_insert hs.to_set, convexJoin_singleton_left]
  simp only [Set.mem_iUnion, segment_eq_image_lineMap, Set.mem_image, exists_prop]

end HodgeLean.Foundations.Program
