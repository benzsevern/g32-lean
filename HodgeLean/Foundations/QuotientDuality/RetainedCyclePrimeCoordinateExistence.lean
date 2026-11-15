import HodgeLean.Foundations.QuotientDuality.RetainedCycleSingletonCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinatesInjective

/-! # Existence of literal prime coordinates from a nonzero supported vector -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero supported vector supplies all actual cap coordinates on a single prime. -/
lemma retained_prime_cap_coordinates_surjective_of_nonzero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : ∀ y ∈ (properPrime ξ).support, Order.coheight y = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (a : s2e_supportedClass X (properPrime ξ) k) (ha : a ≠ 0) :
    Function.Surjective (properCycle_cap_coordinates X k hk hdim (properPrime ξ) hc c) := by
  classical
  have hpoint (y : (properPrime ξ).support) : y.val = ξ := by
    by_contra h
    exact y.property (by simp [properPrime, h])
  letI : Subsingleton (properPrime ξ).support :=
    ⟨fun y z => Subtype.ext ((hpoint y).trans (hpoint z).symm)⟩
  letI : Nonempty (properPrime ξ).support := ⟨⟨ξ, by simp [properPrime]⟩⟩
  exact retained_singleton_coordinates_surjective _
    (properCycle_cap_coordinates_injective X k hk hdim (properPrime ξ) hc c ho hv) a ha

end HodgeLean.Foundations.QuotientDuality
