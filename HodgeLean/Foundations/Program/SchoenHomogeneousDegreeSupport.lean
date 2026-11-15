import HodgeLean.Foundations.Program.SchoenHomogeneousAdjoin

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An algebra generated in degree D has no components outside multiples of D. -/
theorem s2_commonDegreeAdjoin_components_vanish {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (v : ι → A)
    (hv : ∀ i, v i ∈ 𝒜 D) (a : A) (ha : a ∈ Algebra.adjoin (𝒜 0) (Set.range v))
    (n : ℕ) (hn : ¬ D ∣ n) : (DirectSum.decompose 𝒜 a n : A) = 0 := by
  classical
  induction ha using Algebra.adjoin_induction generalizing n with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    apply DirectSum.decompose_of_mem_ne 𝒜 (hv i)
    intro h
    exact hn (h ▸ dvd_refl D)
  | algebraMap c =>
    apply DirectSum.decompose_of_mem_ne 𝒜 c.property
    intro h
    exact hn (h ▸ dvd_zero D)
  | add x y _ _ hx hy =>
    rw [DirectSum.decompose_add]
    change (DirectSum.decompose 𝒜 x n : A) + (DirectSum.decompose 𝒜 y n : A) = 0
    rw [hx n hn, hy n hn, add_zero]
  | mul x y _ _ hx hy =>
    rw [DirectSum.decompose_mul, DirectSum.mul_eq_dfinsuppSum, DFinsupp.sum_apply,
      DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]
    apply Finset.sum_eq_zero
    intro j _
    rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h : n = j + k
    · subst n
      have hnot : ¬ D ∣ j ∨ ¬ D ∣ k := by
        by_contra! h
        exact hn (dvd_add h.1 h.2)
      rcases hnot with hj | hk
      · simp [DirectSum.of_eq_same, hx j hj]
      · simp [DirectSum.of_eq_same, hy k hk]
    · simp [DirectSum.of_eq_of_ne, h]

end HodgeLean.Foundations.Program
