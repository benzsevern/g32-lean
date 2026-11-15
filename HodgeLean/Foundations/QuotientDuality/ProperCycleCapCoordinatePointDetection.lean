import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateSupportFactorization
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSumInjective

/-! # Actual cap coefficients detected by intrinsic component point values
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero isolated intrinsic component point value detects the corresponding actual cap coordinate, with exactly the original common complex cap scalar.
Source: properCycle_cap_coordinates_support_factorization; properCycle_intrinsic_support_sum_point_value; properCycle_standard_complex_cap_scalar_ne_zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_coordinate_point_detection
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ η ∈ γ.support, Order.coheight η = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) (a : s2e_supportedClass X γ k)
    (ξ : γ.support) (z : a3b4_cycleSupport X.hom γ)
    (hother : ∀ η ∈ γ.support, η ≠ ξ.val → z.val.underlying ∉ closure ({η} : Set X.left))
    (m : ℚ)
    (hn : localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
        (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))) z ≠ 0)
    (hp : localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (properCycle_original_support_cap X γ k c a) z =
      (m * properCycle_standard_complex_cap_scalar k k) •
        localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
          (properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
            (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))) z) :
    properCycle_cap_coordinates X k hk hdim γ hc c a ξ = m := by
  let L := (relativeHomologyProjection ℚ
    (pointComplementPair (M := a3b4_cycleSupport X.hom γ) z) (2*k)).hom
  have h := congrArg L (properCycle_cap_coordinates_support_factorization X k hk hdim γ hc c a)
  rw [map_smul] at h
  have hs := properCycle_intrinsic_support_sum_point_value X k hdim γ hc
    (properCycle_cap_coordinates X k hk hdim γ hc c a) ξ z hother
  change L (properCycle_intrinsic_support_sum X k hdim γ hc _) = _ at hs
  rw [hs, smul_smul] at h
  have hvalue := h.symm.trans hp
  have hcoeff := smul_left_injective ℚ hn hvalue
  exact mul_left_cancel₀ (properCycle_standard_complex_cap_scalar_ne_zero k k)
    (hcoeff.trans (mul_comm m (properCycle_standard_complex_cap_scalar k k)))

end HodgeLean.Foundations.QuotientDuality
