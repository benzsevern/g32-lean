import HodgeLean.Foundations.RationalHomologyManifold.AmbientUnitComplex
import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCycleCapComplex
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetInitialNormalization

/-! The actual fixed-cycle cup-unit map into supported-chain homology.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual fixed-cycle cap sends the original cup unit to an initial cocycle of its bounded target.
Source: Hatcher, Algebraic Topology, section 3.3; the cap differential on a fixed cycle.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCap_unit_cocycle (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0) :
    (ambientConstantsToZeroSheaf X ≫ ambientCapTargetComponent X (n + 1) z 0) ≫
      (capTargetComplex X (n + 1)).d 0 1 = 0 := by
  rw [Category.assoc, ← ambientCapTargetComponent_comm_zero X n z hz,
    ← Category.assoc, ambientConstantsToZeroSheaf_coboundary, zero_comp]

#print axioms fixedCycleCap_unit_cocycle
/-- Take actual initial homology of cap by the original cup unit and retain its specified supported-chain homology identification.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
def fixedCycleCapOrientationMap (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0) :
    TopCat.Sheaf.const X (AddCommGrpCat.of ℚ) ⟶
      (subdivisionLimitSheafComplex X).homology (n + 1) :=
  (capTargetComplex X (n + 1)).liftCycles
      (ambientConstantsToZeroSheaf X ≫ ambientCapTargetComponent X (n + 1) z 0)
      1 (CochainComplex.next ℕ 0) (fixedCycleCap_unit_cocycle X n z hz) ≫
    (capTargetComplex X (n + 1)).homologyπ 0 ≫ (capTargetInitialHomologyIso X n).hom

#print axioms fixedCycleCapOrientationMap
/-- The actual cup-unit map into supported homology retains literal fixed-chain cap followed by the original top boundary quotient.
Source: Bredon, Sheaf Theory, second edition, VI.12; normalization on actual initial cycles.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapOrientationMap_inclusion (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0) :
    fixedCycleCapOrientationMap X n z hz ≫ (subdivisionLimitSheafComplex X).homologyι (n + 1) =
      ambientConstantsToZeroSheaf X ≫ ambientFixedCapSheafMap X 0 (n + 1)
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : n + 1 = 0 + (n + 1))).hom z) ≫
          (subdivisionLimitSheafComplex X).pOpcycles (n + 1) := by
  dsimp only [fixedCycleCapOrientationMap]
  simp only [Category.assoc]
  rw [capTargetInitialHomologyIso_cycles, HomologicalComplex.liftCycles_i_assoc,
    Category.assoc, ambientCapTargetComponent_zero]

#print axioms fixedCycleCapOrientationMap_inclusion
end HodgeLean.Foundations.RationalHomologyManifold
