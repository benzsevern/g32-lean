import HodgeLean.Foundations.Program.CompensationAssemblyRelativeProduct
import HodgeLean.Adapters.CycleClassFlatComparisonDefs
import HodgeLean.Adapters.CycleClassDivisorProduct4
import HodgeLean.Adapters.CycleClassDivisorLocalDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison

/-- An arbitrary geometric pullback of a prime class has a relative lift on its inverse support.
Source: naturality of relative cohomology and the supported cycle-class comparison. -/
theorem s4_selected_relative_prime_pullback
    (X Z : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (p : ℕ) (z : Z.left) (hz : Order.coheight z = p) :
    relativeCohomologyToAbsolute ℚ _ (2 * p)
      (relativeCohomologyMap ℚ (2 * p)
        (ccm17_preimagePair (TopCat.of (ComplexPoint X)) (TopCat.of (ComplexPoint Z))
          (Point.continuousMap f) (cycleComponentAnalyticClosedSupport Z z))
        (ccm16_supportedComparison Z (cycleComponentAnalyticClosedSupport Z z) (2 * p)
          (cycleComponentSupportedInjectiveClass Z z hz))) =
      cupComparison X (2 * p) (homPullback f (2 * p) (cycleComponentSheafClass Z z hz)) := by
  have hc : relativeCohomologyToAbsolute ℚ _ (2 * p)
      (ccm16_supportedComparison Z (cycleComponentAnalyticClosedSupport Z z) (2 * p)
        (cycleComponentSupportedInjectiveClass Z z hz)) =
      cupComparison Z (2 * p) (cycleComponentSheafClass Z z hz) :=
    (ccm16_supportedComparison_forget Z (cycleComponentAnalyticClosedSupport Z z) (2 * p)
      (cycleComponentSupportedInjectiveClass Z z hz)).trans
      (bh11_cupComparison_eq_raw Z (2 * p) (cycleComponentSheafClass Z z hz)).symm
  rw [cq_relativeToAbsolute_naturality, hc]
  simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

#print axioms s4_selected_relative_prime_pullback
end HodgeLean.Foundations.Program
