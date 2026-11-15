import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Literal component coordinates extended by zero

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

/-- Extend rational coordinates on the actual prime support of a cycle by zero at every other scheme point.
Source: Fulton, Intersection Theory, section 1.5, cycles as finite sums of primes.
HC no distance; AV milestone no distance. -/
def properCycle_extend_coordinates (X : Scheme.{0}) (γ : AlgebraicCycle X ℚ) :
    (γ.support → ℚ) →ₗ[ℚ] (X → ℚ) := by
  classical
  exact
    { toFun := fun v ξ => if h : ξ ∈ γ.support then v ⟨ξ, h⟩ else 0
      map_add' := by intro v w; funext ξ; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := by intro q v; funext ξ; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

example (X : Scheme.{0}) (ξ : X) :
    properCycle_extend_coordinates X (properPrime ξ) (fun _ => (2 : ℚ)) ξ = 2 := by
  classical
  change (if h : ξ ∈ (properPrime ξ).support then _ else 0) = _
  rw [dif_pos (show ξ ∈ (properPrime ξ).support by simp [properPrime])]

/-- The cycle's literal coefficient vector extends to its original coefficient function.
Source: Fulton, Intersection Theory, section 1.5.
HC no distance; AV milestone no distance. -/
theorem properCycle_extend_literal_coordinates (X : Scheme.{0}) (γ : AlgebraicCycle X ℚ) :
    properCycle_extend_coordinates X γ (fun ξ => γ ξ.val) = γ := by
  classical
  funext ξ
  change (if h : ξ ∈ γ.support then γ ξ else 0) = γ ξ
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp h).symm

example (X : Scheme.{0}) (ξ : X) :
    properCycle_extend_coordinates X (properPrime ξ) (fun _ => (1 : ℚ)) ξ = 1 := by
  classical
  change (if h : ξ ∈ (properPrime ξ).support then _ else 0) = _
  rw [dif_pos (show ξ ∈ (properPrime ξ).support by simp [properPrime])]

end HodgeLean.Foundations.QuotientDuality
