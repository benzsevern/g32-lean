import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportBasisNaturality

/-! # Literal support enlargement for actual cap coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Constructed cap coordinates commute with the original supported cohomology enlargement map after literal zero extension at the actual scheme points.
Source: properCycle_original_support_cap_enlarge_support; properCycle_intrinsic_support_basis_enlarge.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_coordinates_enlarge
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ δ : AlgebraicCycle X.left ℚ)
    (hcγ : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (hcδ : ∀ ξ ∈ δ.support, Order.coheight ξ = k)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) (a : s2e_supportedClass X γ k) :
    properCycle_extend_coordinates X.left δ
      (properCycle_cap_coordinates X k hk hdim δ hcδ c
        (enlargeSupport ℚ (a3b4_an X.hom) h (2*k) a)) =
      properCycle_extend_coordinates X.left γ
        (properCycle_cap_coordinates X k hk hdim γ hcγ c a) := by
  have he := properCycle_intrinsic_support_basis_enlarge X k hk hdim γ δ hcγ hcδ h
    (properCycle_original_support_cap X γ k c a)
  rw [properCycle_original_support_cap_enlarge_support X γ δ k h c a] at he
  change properCycle_extend_coordinates X.left δ
      ((properCycle_standard_complex_cap_scalar k k)⁻¹ •
        (properCycle_intrinsic_support_basis X k hk hdim δ hcδ).symm
          (properCycle_original_support_cap X δ k c (enlargeSupport ℚ (a3b4_an X.hom) h (2*k) a))) =
    properCycle_extend_coordinates X.left γ
      ((properCycle_standard_complex_cap_scalar k k)⁻¹ •
        (properCycle_intrinsic_support_basis X k hk hdim γ hcγ).symm
          (properCycle_original_support_cap X γ k c a))
  rw [map_smul, map_smul]
  exact congrArg (fun v => (properCycle_standard_complex_cap_scalar k k)⁻¹ • v) he

end HodgeLean.Foundations.QuotientDuality
