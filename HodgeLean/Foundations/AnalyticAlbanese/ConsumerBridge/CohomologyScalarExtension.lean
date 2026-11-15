import HodgeLean.Adapters.HolomorphicPeriodsComparisonProofs
import HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge.DualScalarExtension

/-! # Scalar extension of actual singular cohomology
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters
open scoped TensorProduct
namespace HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge

/-- Scalar extension of singular cohomology is bijective when rational homology is finite.
HC no distance; AV milestone no distance. -/
theorem cohomologyBaseChange_bijective (X : TopCat) (n : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Singular.Homology ℚ X n)] :
    Function.Bijective (cohomologyBaseChange X n) := by
  unfold cohomologyBaseChange
  exact (cohomologyEquivDualHomology ℂ X n).symm.bijective.comp
    ((Module.Dual.congr (complexHomologyEquivBaseChange X n)).bijective.comp
      (dualScalarExtension_bijective (cohomologyEquivDualHomology ℚ X n)))

end HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge
