import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapOrientationMap
import HodgeLean.Foundations.RationalHomologyManifold.ScalarCycleSheafInclusion

/-! Actual unit cap as the original supported scalar homology class.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual cup-unit cap in supported-chain homology is the original scalar cycle class followed by the actual stage-zero subdivision homology map.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapOrientationMap_scalar_class (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0) :
    fixedCycleCapOrientationMap X n z hz =
      scalarCycleHomologySheafMap X n z (hz n) ≫
        HomologicalComplex.homologyMap (subdivisionSheafStage X 0) (n + 1) := by
  apply (cancel_mono ((subdivisionLimitSheafComplex X).homologyι (n + 1))).mp
  rw [fixedCycleCapOrientationMap_inclusion, Category.assoc,
    HomologicalComplex.homologyι_naturality]
  simp only [← Category.assoc]
  rw [scalarCycleHomologySheafMap_inclusion]
  simp only [Category.assoc]
  rw [HomologicalComplex.p_opcyclesMap]
  simp only [← Category.assoc]
  rw [← scalarChainSheafMap_unit_cap]

#print axioms fixedCycleCapOrientationMap_scalar_class
end HodgeLean.Foundations.RationalHomologyManifold
