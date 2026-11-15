import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentOnSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleCoordinateSupportSum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Actual intrinsic component sums on literal middle cycle supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Literal rational component coordinates give their actual sum of specified intrinsic classes in homology of the original support.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1, rational prime sums and intrinsic fundamental classes.
HC no distance; AV milestone no distance. -/
def properCycle_intrinsic_support_sum
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k) :
    (γ.support → ℚ) →ₗ[ℚ] Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k) := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  exact Fintype.linearCombination ℚ (fun ξ : γ.support =>
    properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
      (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property)))

/-- The actual support sum retains precisely the whole-space finite sum of original intrinsic component classes and literal zero-extended coordinates.
Source: Fulton, Intersection Theory, section 19.1; properCycle_intrinsic_component_on_support_inclusion.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_sum_inclusion
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (v : γ.support → ℚ) :
    homologyMap ℚ (2*k) (TopPair.ofSubset (X := a3b4_an X.hom)
      (a3b4_cycleSupport X.hom γ)).map (properCycle_intrinsic_support_sum X k hdim γ hc v) =
      ∑ᶠ ξ, properCycle_extend_coordinates X.left γ v ξ • properCycle_intrinsic_component X k ξ := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  rw [← properCycle_coordinate_support_sum γ (properCycle_intrinsic_component X k) v,
    finsum_eq_sum_of_fintype]
  change homologyMap ℚ (2*k) (TopPair.ofSubset (X := a3b4_an X.hom)
    (a3b4_cycleSupport X.hom γ)).map
    (∑ ξ : γ.support, v ξ • properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
      (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [map_smul, properCycle_intrinsic_component_on_support_inclusion]

end HodgeLean.Foundations.QuotientDuality
