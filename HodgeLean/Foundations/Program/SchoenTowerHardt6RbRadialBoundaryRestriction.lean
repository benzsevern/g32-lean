import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRadialHomeomorph

/-! Exact boundary values and intrinsic interior preservation of radial extensions. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_radial_boundary_restriction {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : Set E) (D : Set F) (hc : Convex ℝ C)
    (a : E) (b : F) (ha : a ∈ intrinsicInterior ℝ C)
    (h : ↥(C \ intrinsicInterior ℝ C) ≃ₜ ↥(D \ intrinsicInterior ℝ D))
    (H : C ≃ₜ D)
    (hH : ∀ x : ↥(C \ intrinsicInterior ℝ C), ∀ t : Set.Icc (0 : ℝ) 1,
      (H ⟨AffineMap.lineMap a x.val t.val,
        hc.segment_subset (intrinsicInterior_subset ha) x.property.1
          (lineMap_mem_segment ℝ a x.val t.property)⟩).val =
        AffineMap.lineMap b (h x).val t.val) :
    (∀ x : ↥(C \ intrinsicInterior ℝ C), (H ⟨x.val, x.property.1⟩).val = (h x).val) ∧
    (∀ x : C, (H x).val ∈ intrinsicInterior ℝ D ↔ x.val ∈ intrinsicInterior ℝ C) := by
  have hboundary : ∀ x : ↥(C \ intrinsicInterior ℝ C),
      (H ⟨x.val, x.property.1⟩).val = (h x).val := by
    intro x
    simpa only [AffineMap.lineMap_apply_one] using hH x ⟨1, zero_le_one, le_rfl⟩
  refine ⟨hboundary, ?_⟩
  intro x
  constructor
  · intro hx
    by_contra hn
    have he := hboundary ⟨x.val, x.property, hn⟩
    exact (h ⟨x.val, x.property, hn⟩).property.2 (he ▸ hx)
  · intro hx
    by_contra hn
    let y : ↥(D \ intrinsicInterior ℝ D) := ⟨(H x).val, (H x).property, hn⟩
    let z := h.symm y
    have he : H ⟨z.val, z.property.1⟩ = H x := by
      apply Subtype.ext
      exact (hboundary z).trans (congrArg Subtype.val (h.apply_symm_apply y))
    have hz : z.val = x.val := congrArg Subtype.val (H.injective he)
    exact z.property.2 (hz.symm ▸ hx)

end HodgeLean.Foundations.Program
