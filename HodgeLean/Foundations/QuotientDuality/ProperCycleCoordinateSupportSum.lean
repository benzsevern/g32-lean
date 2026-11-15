import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCoordinates
import Mathlib.Algebra.BigOperators.Finprod

/-! # Actual component sums with literal extension by zero
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

/-- A sum over actual prime coordinates is exactly the original whole-space sum with those coordinates extended by zero.
Source: Fulton, Intersection Theory, section 1.5, finite prime sums and extension by zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_coordinate_support_sum
    {X : Scheme.{0}} (γ : AlgebraicCycle X ℚ)
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (C : X → W) (v : γ.support → ℚ) :
    (∑ᶠ ξ : γ.support, v ξ • C ξ.val) =
      ∑ᶠ ξ, properCycle_extend_coordinates X γ v ξ • C ξ := by
  classical
  let f : X → W := fun ξ => properCycle_extend_coordinates X γ v ξ • C ξ
  calc
    _ = ∑ᶠ ξ : γ.support, f ξ.val := by
      apply finsum_congr
      intro ξ
      change v ξ • C ξ.val =
        (if h : ξ.val ∈ γ.support then v ⟨ξ.val, h⟩ else 0) • C ξ.val
      rw [dif_pos ξ.property]
    _ = ∑ᶠ ξ ∈ γ.support, f ξ := finsum_set_coe_eq_finsum_mem γ.support
    _ = _ := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro ξ
      by_cases hξ : ξ ∈ γ.support
      · rw [Set.indicator_of_mem hξ]
      · rw [Set.indicator_of_notMem hξ]
        change 0 = (if h : ξ ∈ γ.support then v ⟨ξ, h⟩ else 0) • C ξ
        rw [dif_neg hξ, zero_smul]

end HodgeLean.Foundations.QuotientDuality
