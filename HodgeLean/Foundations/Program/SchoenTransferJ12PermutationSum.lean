import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A sum over finite endomaps supported on surjections is exactly the permutation sum. -/
theorem s4_selected_sum_endomaps_on_surjections
    {α V : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid V]
    (F : (α → α) → V) (hF : ∀ a, ¬ Function.Surjective a → F a = 0) :
    ∑ a : α → α, F a = ∑ σ : Equiv.Perm α, F σ := by
  classical
  calc
    ∑ a : α → α, F a =
        ∑ a ∈ Finset.univ.filter Function.Surjective, F a := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a ha hnot
      exact hF a (by simpa only [Finset.mem_filter, ha, true_and] using hnot)
    _ = ∑ σ : Equiv.Perm α, F σ := by
      refine Finset.sum_bij
        (fun a ha => Equiv.ofBijective a
          ⟨Finite.injective_iff_surjective.mpr (Finset.mem_filter.mp ha).2,
            (Finset.mem_filter.mp ha).2⟩) ?_ ?_ ?_ ?_
      · intro a ha
        exact Finset.mem_univ _
      · intro a ha b hb hab
        exact congrArg (fun σ : Equiv.Perm α => (σ : α → α)) hab
      · intro σ hσ
        refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.surjective⟩, ?_⟩
        ext i
        rfl
      · intro a ha
        rfl

#print axioms s4_selected_sum_endomaps_on_surjections
end HodgeLean.Foundations.Program
