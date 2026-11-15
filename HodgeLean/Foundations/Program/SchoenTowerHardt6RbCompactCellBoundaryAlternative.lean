import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactRayEndpoint

/-! A compact carrier with an intrinsic interior center is a singleton or has an actual intrinsic boundary point. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_cell_boundary_alternative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : IsCompact C) (a : E) (ha : a ∈ intrinsicInterior ℝ C) :
    (∃ p, C = {p}) ∨ (C \ intrinsicInterior ℝ C).Nonempty := by
  classical
  by_cases hpoint : ∀ x ∈ C, x = a
  · left
    refine ⟨a, Set.Subset.antisymm ?_ ?_⟩
    · intro x hx
      exact hpoint x hx
    · rintro x rfl
      exact intrinsicInterior_subset ha
  · right
    push_neg at hpoint
    obtain ⟨x, hx, hxa⟩ := hpoint
    obtain ⟨y, hy, _, _, _⟩ := s2v_hardt6rb_compact_ray_endpoint C hC a
      (intrinsicInterior_subset ha) x hx hxa
    exact ⟨y, hy⟩

end HodgeLean.Foundations.Program
