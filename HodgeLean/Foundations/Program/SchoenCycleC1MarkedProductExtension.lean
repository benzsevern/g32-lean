import HodgeLean.Foundations.Program.SchoenCycleC1MarkedProductReindex
import Mathlib.Algebra.GroupWithZero.Units.Basic

noncomputable section
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Extending the selected marked generators by one gives an exact signed
product over every original label. -/
theorem s2e_c1_marked_product_extension
    {I P R K : Type*} [Fintype I] [DecidableEq P] [CommMonoid R]
    [CommGroupWithZero K]
    (marks : I → P) (hinj : Function.Injective marks) (A : Finset P)
    (b : A → R) (φ : R →* K) (n : P → ℤ) :
    ∃ g : I → R,
      (∀ i (hi : marks i ∈ A), g i = b ⟨marks i, hi⟩) ∧
      (∀ i, marks i ∉ A → g i = 1) ∧
      (∏ j ∈ Finset.univ.filter (fun j : A => ∃ i, j.val = marks i),
        (φ (b j)) ^ n j.val) = ∏ i, (φ (g i)) ^ n (marks i) := by
  classical
  let g : I → R := fun i => if hi : marks i ∈ A then b ⟨marks i, hi⟩ else 1
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i hi
    exact dif_pos hi
  · intro i hi
    exact dif_neg hi
  · rw [s2e_c1_marked_product_reindex marks hinj A]
    have hsub := Finset.prod_subtype
      (p := fun i : I => marks i ∈ A) (F := inferInstance)
      (Finset.univ.filter (fun i : I => marks i ∈ A)) (by simp)
      (fun i => (φ (g i)) ^ n (marks i))
    have heq : (∏ i : {i : I // marks i ∈ A}, (φ (b ⟨marks i.val, i.property⟩)) ^ n (marks i.val)) =
        ∏ i ∈ Finset.univ.filter (fun i : I => marks i ∈ A), (φ (g i)) ^ n (marks i) := by
      rw [hsub]
      apply Finset.prod_congr rfl
      intro i _
      simp only [g, dif_pos i.property]
    rw [heq]
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hnot : marks i ∉ A := by simpa using hi
    simp [g, hnot]

end HodgeLean.Foundations.Program
