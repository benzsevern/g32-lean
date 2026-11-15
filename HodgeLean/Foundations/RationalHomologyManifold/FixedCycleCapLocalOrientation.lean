import HodgeLean.Foundations.RationalHomologyManifold.FixedCapScalarHomologyComparison
import HodgeLean.Foundations.RationalHomologyManifold.ScalarCycleOrientation
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetOrientation

/-! Actual fixed-cycle unit cap realizes the specified local orientation.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual cup-unit fixed-cycle cap map into supported homology is invertible when the cycle has the specified local generators.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; normalization of actual local cap by the unit.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapOrientationMap_isIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z (hz n))) = o.generator) :
    IsIso (fixedCycleCapOrientationMap X n z hz) := by
  rw [fixedCycleCapOrientationMap_scalar_class,
    scalarCycleHomologySheafMap_orientation X n o z (hz n) hc]
  letI := subdivisionSheafStage_quasiIso X 0
  infer_instance

#print axioms fixedCycleCapOrientationMap_isIso
end HodgeLean.Foundations.RationalHomologyManifold
