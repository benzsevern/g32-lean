import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Basic

/-! Retained branch exponents in an etale chart's coordinate indices.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Extending retained exponents by zero preserves the monomial under the chart embedding.
Source: reindexing a finite product along an injection. -/
theorem s2v_i2b_branch_exponents_reindex
    {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommMonoid M]
    (J : Finset ι) (e : J ↪ κ) (α : ι → ℕ) (z : ι → M) (w : κ → M)
    (hz : ∀ t : J, z t = w (e t)) (habsent : ∀ t, t ∉ J → z t = 1) :
    ∃ β : κ → ℕ, (∀ t : J, β (e t) = α t) ∧
      (∏ t, z t ^ α t) = ∏ j, w j ^ β j := by
  classical
  let β : κ → ℕ := Function.extend e (fun t : J => α t) (fun _ => 0)
  have hβ : ∀ t : J, β (e t) = α t := e.injective.extend_apply _ _
  refine ⟨β, hβ, ?_⟩
  calc
    (∏ t, z t ^ α t) = ∏ t ∈ J, z t ^ α t := by
      symm
      apply Finset.prod_subset (Finset.subset_univ J)
      intro t _ ht
      rw [habsent t ht, one_pow]
    _ = ∏ t : J, z t ^ α t := (Finset.prod_coe_sort J (fun t => z t ^ α t)).symm
    _ = ∏ t : J, w (e t) ^ α t := by
      apply Finset.prod_congr rfl
      intro t _
      rw [hz t]
    _ = ∏ j, w j ^ β j := by
      apply Fintype.prod_of_injective e e.injective
      · intro j hj
        have hjβ : β j = 0 := Function.extend_apply' _ _ j hj
        rw [hjβ, pow_zero]
      · intro t
        rw [hβ t]

end HodgeLean.Foundations.Program
