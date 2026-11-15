import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Any natural number below a finite sum can be allocated within the summands' bounds. -/
theorem s2_exists_bounded_sum {ι : Type} (s : Finset ι) (a : ι → ℕ)
    (m : ℕ) (hm : m ≤ ∑ i ∈ s, a i) :
    ∃ b : ι → ℕ, (∀ i, b i ≤ a i) ∧ ∑ i ∈ s, b i = m := by
  classical
  induction s using Finset.induction generalizing m with
  | empty =>
    refine ⟨0, fun i => Nat.zero_le _, ?_⟩
    simpa only [Finset.sum_empty] using Nat.eq_zero_of_le_zero hm |>.symm
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi] at hm
    by_cases hmi : m ≤ a i
    · refine ⟨Pi.single i m, ?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j; simpa only [Pi.single_eq_same] using hmi
        · simp only [Pi.single_eq_of_ne hji, Nat.zero_le]
      · rw [Finset.sum_insert hi, Pi.single_eq_same]
        have hz : ∑ j ∈ s, Pi.single i m j = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          exact Pi.single_eq_of_ne ((show j ≠ i from fun h => hi (h ▸ hj))) _
        rw [hz, add_zero]
    · obtain ⟨b, hb, hsum⟩ := ih (m - a i) (by omega)
      refine ⟨Function.update b i (a i), ?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j; simp only [Function.update_self, le_refl]
        · rw [Function.update_of_ne hji]; exact hb j
      · rw [Finset.sum_insert hi, Function.update_self]
        have hs : ∑ j ∈ s, Function.update b i (a i) j = ∑ j ∈ s, b j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Function.update_of_ne ((show j ≠ i from fun h => hi (h ▸ hj))) _ _
        rw [hs, hsum]
        omega

end HodgeLean.Foundations.Program
