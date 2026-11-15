import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicExtension

/-! A cone simplex meets the intrinsic boundary exactly in the hull of its vertices avoiding the apex. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_boundary_hull {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Convex ℝ C) (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    (s : Finset E)
    (hs : convexHull ℝ (↑(s.erase a) : Set E) ⊆ C \ intrinsicInterior ℝ C) :
    convexHull ℝ (s : Set E) ∩ (C \ intrinsicInterior ℝ C) =
      convexHull ℝ (↑(s.erase a) : Set E) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxC, hxn⟩
    by_cases has : a ∈ s
    · by_cases hne : (s.erase a).Nonempty
      · have he : insert a (s.erase a) = s := Finset.insert_erase has
        obtain ⟨y, hy, t, ht, htx⟩ := (s2v_hardt6rb_cone_coordinates a (s.erase a) hne x).mp (by simpa only [he] using hx)
        have ht1 : t = 1 := by
          by_contra hn
          have htlt : t < 1 := lt_of_le_of_ne ht.2 hn
          by_cases ht0 : t = 0
          · have hxa : x = a := by simpa only [ht0, AffineMap.lineMap_apply_zero] using htx.symm
            exact hxn (hxa ▸ ha)
          · have hp : x ∈ openSegment ℝ a y := by
              rw [← htx]
              exact lineMap_mem_openSegment ℝ a y ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), htlt⟩
            exact hxn (hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior ha
              (subset_intrinsicClosure (hs hy).1) hp)
        have hxy : x = y := by simpa only [ht1, AffineMap.lineMap_apply_one] using htx.symm
        exact hxy ▸ hy
      · have he : s.erase a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hsone : s = {a} := by
          calc
            s = insert a (s.erase a) := (Finset.insert_erase has).symm
            _ = {a} := by rw [he]; rfl
        have hxa : x = a := by simpa only [hsone, Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hx
        exact False.elim (hxn (hxa ▸ ha))
    · simpa only [Finset.erase_eq_of_notMem has] using hx
  · intro x hx
    exact ⟨convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset a s)) hx, hs hx⟩

end HodgeLean.Foundations.Program
