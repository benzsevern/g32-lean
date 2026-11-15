import HodgeLean.Adapters.KleimanProductLocal
import HodgeLean.Adapters.NormalConeB4Defs

/-! Naturality of the specified supported comparison under support enlargement. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Enlarging an actual sheaf support and enlarging its ambient singular pair
commute under the constructed comparison. -/
theorem s4_q3_supportedComparison_enlarge
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ)
    (u : H_[S]^n(X; ℚ)) :
    ccm16_supportedComparison X T n (supportEnlarge X h n u) =
      relativeCohomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of (ComplexPoint X)) (SetLike.coe_subset_coe.mpr h))
        (ccm16_supportedComparison X S n u) := by
  change relativeCohomologyMap ℚ n (ccm16_fullPairIso (TopCat.of (ComplexPoint X)) T).hom
      (supportedSingularClass X T n (supportEnlarge X h n u)) = _
  rw [supportedSingularClass_restrict]
  change ((relativeCohomologyMap ℚ n (ccm16_fullPairIso (TopCat.of (ComplexPoint X)) T).hom).comp
    (relativeCohomologyMap ℚ n (neighborhoodSupportEnlargePairMap _
      (SetLike.coe_subset_coe.mpr h)))) (supportedSingularClass X S n u) = _
  rw [← relativeCohomologyMap_comp]
  change _ = ((relativeCohomologyMap ℚ n
    (supportInclusionPairMap (TopCat.of (ComplexPoint X)) (SetLike.coe_subset_coe.mpr h))).comp
    (relativeCohomologyMap ℚ n (ccm16_fullPairIso (TopCat.of (ComplexPoint X)) S).hom))
      (supportedSingularClass X S n u)
  rw [← relativeCohomologyMap_comp]
  rfl

/-- Equality after restricting the actual ambient comparisons gives equality
of supported sheaf germs at every point of that neighbourhood. -/
theorem s4_q3_supportGerm_eq_of_comparison_restriction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) (x : ComplexPoint X)
    (V : Opens (ComplexPoint X)) (hx : x ∈ V)
    (u v : H_[S]^n(X; ℚ))
    (h : relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap (V : Set (ComplexPoint X)) S)
        (ccm16_supportedComparison X S n u) =
      relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap (V : Set (ComplexPoint X)) S)
        (ccm16_supportedComparison X S n v)) :
    ccm5_supportGerm X S n x u = ccm5_supportGerm X S n x v := by
  rw [← ccm5_supportGerm_restriction X S V n x hx u,
    ← ccm5_supportGerm_restriction X S V n x hx v]
  apply congrArg (supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X)) S n V x hx)
  rw [← hc9k_supportedComparison_restrict, ← hc9k_supportedComparison_restrict]
  exact h

end HodgeLean.Foundations.Program
