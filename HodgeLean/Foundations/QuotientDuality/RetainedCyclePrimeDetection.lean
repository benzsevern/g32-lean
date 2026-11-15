import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinatesInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateAbsoluteFactorization

/-! Prime-carrier detection through the actual intrinsic component image. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- The zero-extended coordinate sum of a prime has its single literal component value. -/
lemma retained_prime_coordinate_sum
    (X : Scheme.{0}) (ξ : X) {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : X → V) (w : (properPrime ξ).support → ℚ) :
    (∑ᶠ η, properCycle_extend_coordinates X (properPrime ξ) w η • v η) =
      w ⟨ξ, by simp [properPrime]⟩ • v ξ := by
  rw [finsum_eq_single _ ξ]
  · change (if h : ξ ∈ (properPrime ξ).support then w ⟨ξ, h⟩ else 0) • v ξ = _
    rw [dite_eq_left (by simp [properPrime])]
  · intro η hη
    have hn : η ∉ (properPrime ξ).support := by simp [properPrime, hη]
    change (if h : η ∈ (properPrime ξ).support then w ⟨η, h⟩ else 0) • v η = 0
    rw [dite_eq_right hn, zero_smul]

/-- A nonzero intrinsic prime image lets the actual cap coordinates detect forgotten prime classes. -/
lemma retained_prime_forget_injective_of_intrinsic_ne_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (hξ : properCycle_intrinsic_component X k ξ ≠ 0) :
    Function.Injective (s2e_classToAbsolute X (properPrime ξ) k) := by
  have hcodim : ∀ η ∈ (properPrime ξ).support, Order.coheight η = k := by
    intro η hη
    have he : η = ξ := by
      by_contra hn
      exact hη (by simp [properPrime, hn])
    simpa only [he] using hc
  intro a b hab
  let E := properCycle_cap_coordinates X k hk hdim (properPrime ξ) hcodim c
  have ha := properCycle_cap_coordinates_absolute_factorization
    X k hk hdim (properPrime ξ) hcodim c a
  have hb := properCycle_cap_coordinates_absolute_factorization
    X k hk hdim (properPrime ξ) hcodim c b
  rw [hab] at ha
  have he := ha.symm.trans hb
  rw [retained_prime_coordinate_sum, retained_prime_coordinate_sum] at he
  have hvect := smul_right_injective _
    (properCycle_standard_complex_cap_scalar_ne_zero k k) he
  have hq := smul_left_injective ℚ hξ hvect
  apply properCycle_cap_coordinates_injective X k hk hdim (properPrime ξ) hcodim c ho hv
  funext η
  have hη : η.val = ξ := by
    by_contra hn
    exact η.property (by simp [properPrime, hn])
  have hη' : η = ⟨ξ, by simp [properPrime]⟩ := Subtype.ext hη
  rw [hη']
  exact hq

end HodgeLean.Foundations.QuotientDuality
