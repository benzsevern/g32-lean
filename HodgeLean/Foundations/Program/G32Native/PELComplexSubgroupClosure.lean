import HodgeLean.Foundations.HodgeGroupAlgebraicDescent

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Complex Zariski closure preserves subgroups. This statement needs no
Galois invariance or rationality of the original subgroup.
Source: Borel, Linear Algebraic Groups, second edition, §1.3. -/
theorem pelComplexSubgroupClosure {n : ℕ}
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
    ∃ K : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ),
      (K : Set _) = @closure _ (g1_zariski ℂ n) (H : Set _) := by
  letI : TopologicalSpace (Matrix.GeneralLinearGroup (Fin n) ℂ) := g1_zariski ℂ n
  let C := closure (H : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
  have hC : IsClosed C := isClosed_closure
  have hleft : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C := by
    intro h hh x hx
    have hm := image_closure_subset_closure_image (g1_continuous_mul_left h) ⟨x, hx, rfl⟩
    apply closure_mono _ hm
    rintro _ ⟨y, hy, rfl⟩
    exact H.mul_mem hh hy
  have hmul : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C := by
    intro x hx y hy
    have hm := image_closure_subset_closure_image (g2h_continuous_mul_right y) ⟨x, hx, rfl⟩
    apply closure_minimal _ hC hm
    rintro _ ⟨h, hh, rfl⟩
    exact hleft h hh y hy
  have hone : (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) ∈ C := subset_closure H.one_mem
  have hinv : ∀ x ∈ C, x⁻¹ ∈ C := by
    intro x hx
    have := g1_noetherianSpace (k := ℂ) (n := n)
    let Z : ℕ → TopologicalSpace.Closeds (Matrix.GeneralLinearGroup (Fin n) ℂ) := fun j =>
      ⟨(fun y => x ^ j * y) '' C, by
        rw [Set.image_mul_left]
        exact hC.preimage (g1_continuous_mul_left _)⟩
    obtain ⟨_, ⟨j, rfl⟩, hmin⟩ :=
      (wellFounded_lt (α := TopologicalSpace.Closeds _)).has_min (Set.range Z) ⟨Z 0, 0, rfl⟩
    have hle : Z (j + 1) ≤ Z j := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨x * y, hmul x hx y hy, by simp only [pow_succ, mul_assoc]⟩
    have heq : Z (j + 1) = Z j := by
      by_contra hne
      exact hmin _ ⟨j + 1, rfl⟩ (lt_of_le_of_ne hle hne)
    have hxj : x ^ j ∈ (Z j : Set _) := ⟨1, hone, mul_one _⟩
    rw [← heq] at hxj
    obtain ⟨y, hy, hxy⟩ := hxj
    have he : y = x⁻¹ := by
      simp only [pow_succ, mul_assoc] at hxy
      have hh := mul_left_cancel (a := x ^ j) (hxy.trans (mul_one _).symm)
      exact eq_inv_of_mul_eq_one_right hh
    exact he ▸ hy
  exact ⟨{ carrier := C
           one_mem' := hone
           mul_mem' := fun hx hy => hmul _ hx _ hy
           inv_mem' := fun hx => hinv _ hx }, rfl⟩

#print axioms pelComplexSubgroupClosure
end HodgeLean.Foundations.Program.GeneralTypeIII
