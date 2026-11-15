import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicExtension

/-! A nonnegative affine function positive somewhere is positive on every intrinsic interior point. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_interior_positive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (f : E →ᵃ[ℝ] ℝ) (hn : ∀ x ∈ C, 0 ≤ f x)
    (hy : ∃ y ∈ C, 0 < f y) {x : E} (hx : x ∈ intrinsicInterior ℝ C) :
    0 < f x := by
  obtain ⟨y, hyC, hyf⟩ := hy
  obtain ⟨t, ht, hz⟩ := s2v_hardt6rb_intrinsicInterior_extend C hx hyC
  have he : f (x + t • (x - y)) = f x + t * (f x - f y) := by
    rw [add_comm x]
    change f (t • (x -ᵥ y) +ᵥ x) = _
    rw [f.map_vadd, map_smul, f.linear_apply_vsub]
    simp only [vadd_eq_add, vsub_eq_sub, smul_eq_mul]
    ring
  have hh := hn _ hz
  rw [he] at hh
  have hnX := hn x (intrinsicInterior_subset hx)
  by_contra h
  have heX : f x = 0 := le_antisymm (le_of_not_gt h) hnX
  rw [heX] at hh
  nlinarith

end HodgeLean.Foundations.Program
