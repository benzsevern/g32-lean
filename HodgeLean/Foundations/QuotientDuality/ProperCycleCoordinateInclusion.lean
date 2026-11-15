import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCoordinates

/-! # Literal coefficient inclusion between finite prime supports
HC no distance; AV milestone no distance. -/

noncomputable section
open AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

/-- Restrict the literal zero extension of a coefficient vector to another prime support.
Source: Fulton, Intersection Theory, section 1.5, finite prime coefficients.
HC no distance; AV milestone no distance. -/
def properCycle_include_coordinates (X : Scheme.{0}) (γ δ : AlgebraicCycle X ℚ) :
    (γ.support → ℚ) →ₗ[ℚ] (δ.support → ℚ) where
  toFun v η := properCycle_extend_coordinates X γ v η.val
  map_add' v w := by ext η; exact congrFun (map_add (properCycle_extend_coordinates X γ) v w) η.val
  map_smul' q v := by ext η; exact congrFun (map_smul (properCycle_extend_coordinates X γ) q v) η.val

/-- When the literal source primes occur in the target, extending after coefficient inclusion retains the original zero extension.
Source: Fulton, Intersection Theory, section 1.5, extension by zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_extend_include_coordinates (X : Scheme.{0}) (γ δ : AlgebraicCycle X ℚ)
    (h : γ.support ⊆ δ.support) (v : γ.support → ℚ) :
    properCycle_extend_coordinates X δ (properCycle_include_coordinates X γ δ v) =
      properCycle_extend_coordinates X γ v := by
  classical
  funext ξ
  change (if hδ : ξ ∈ δ.support then
    properCycle_extend_coordinates X γ v ξ else 0) = _
  split_ifs with hδ
  · rfl
  · change 0 = (if hγ : ξ ∈ γ.support then v ⟨ξ, hγ⟩ else 0)
    rw [dif_neg (fun hγ => hδ (h hγ))]

/-- Literal inclusion of prime sets makes the coefficient inclusion injective.
Source: properCycle_extend_include_coordinates; extension by zero at the original primes.
HC no distance; AV milestone no distance. -/
lemma properCycle_include_coordinates_injective (X : Scheme.{0}) (γ δ : AlgebraicCycle X ℚ)
    (h : γ.support ⊆ δ.support) :
    Function.Injective (properCycle_include_coordinates X γ δ) := by
  classical
  intro v w he
  funext ξ
  have hh := congrFun he (⟨ξ.val, h ξ.property⟩ : δ.support)
  change (if hγ : ξ.val ∈ γ.support then v ⟨ξ.val, hγ⟩ else 0) =
    (if hγ : ξ.val ∈ γ.support then w ⟨ξ.val, hγ⟩ else 0) at hh
  simpa only [dif_pos ξ.property] using hh

end HodgeLean.Foundations.QuotientDuality
