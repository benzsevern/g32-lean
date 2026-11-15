import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryRayUnique

/-! The only identifications in a convex boundary cone occur at its apex. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_fiber_equality {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Convex ℝ C) (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    {x y : E} (hx : x ∈ C \ intrinsicInterior ℝ C)
    (hy : y ∈ C \ intrinsicInterior ℝ C) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    AffineMap.lineMap a x t = AffineMap.lineMap a y u ↔ t = u ∧ (t = 0 ∨ x = y) := by
  have hax : a ≠ x := fun h => hx.2 (h ▸ ha)
  have hay : a ≠ y := fun h => hy.2 (h ▸ ha)
  constructor
  · intro he
    by_cases ht0 : t = 0
    · have hu0 : u = 0 := by
        apply (AffineMap.lineMap_eq_left_iff.mp ?_).resolve_left hay
        simpa only [ht0, AffineMap.lineMap_apply_zero] using he.symm
      exact ⟨ht0.trans hu0.symm, Or.inl ht0⟩
    · have hu0 : u ≠ 0 := by
        intro hu0
        apply ht0
        apply (AffineMap.lineMap_eq_left_iff.mp ?_).resolve_left hax
        simpa only [hu0, AffineMap.lineMap_apply_zero] using he
      obtain ⟨htu, hxy⟩ := s2v_hardt6rb_boundary_ray_unique C hC a ha hx hy
        (lt_of_le_of_ne ht (Ne.symm ht0)) (lt_of_le_of_ne hu (Ne.symm hu0)) he
      exact ⟨htu, Or.inr hxy⟩
  · rintro ⟨rfl, ht0 | hxy⟩
    · simp only [ht0, AffineMap.lineMap_apply_zero]
    · rw [hxy]

end HodgeLean.Foundations.Program
