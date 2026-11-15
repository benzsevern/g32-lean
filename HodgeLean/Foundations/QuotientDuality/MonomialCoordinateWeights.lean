import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Collecting branch-label exponents along the actual coordinate map. -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem branch_product_coordinate_weights
    {R J I : Type*} [CommMonoid R] [Fintype J] [Fintype I]
    (A : Set J) (g : A → I) (z : I → R) (s : J → R) (α : J → ℕ)
    (hpresent : ∀ t : A, s t = z (g t)) (habsent : ∀ t, t ∉ A → s t = 1) :
    ∃ β : I → ℕ, (∏ t, s t ^ α t) = ∏ i, z i ^ β i := by
  classical
  let β : I → ℕ := fun i => ∑ t ∈ Finset.univ.filter (fun t : A => g t = i), α t
  have hprod : (∏ t, s t ^ α t) = ∏ t : A, z (g t) ^ α t := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun t => t ∈ A) (fun t => s t ^ α t)]
    have hc : (∏ t : {t : J // t ∉ A}, s t ^ α t) = 1 := by
      apply Finset.prod_eq_one
      intro t _
      rw [habsent t t.property, one_pow]
    rw [hc, mul_one]
    apply Finset.prod_congr rfl
    intro t _
    rw [hpresent t]
  refine ⟨β, hprod.trans ?_⟩
  symm
  calc
    (∏ i, z i ^ β i) = ∏ i, ∏ t ∈ Finset.univ.filter (fun t : A => g t = i), z i ^ α t := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Finset.prod_pow_eq_pow_sum _ (fun t : A => α t) (z i)).symm
    _ = ∏ i, ∏ t ∈ Finset.univ.filter (fun t : A => g t = i), z (g t) ^ α t := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = ∏ t : A, z (g t) ^ α t := Finset.prod_fiberwise _ g _

#print axioms branch_product_coordinate_weights
end HodgeLean.Foundations.QuotientDuality
