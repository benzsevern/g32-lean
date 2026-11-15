import HodgeLean.Foundations.Program.CompensationAssemblyPrismAbsolute
import HodgeLean.Adapters.HolomorphicPeriodsCocycleProofs

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

def cq_circleLoopClass : Homology ℚ (TopCat.of UnitAddCircle) 1 :=
  ((SingularChainComplex ℚ (TopCat.of UnitAddCircle)).sc 1).moduleCatHomologyClass
    (loopCycle ℚ (ContinuousMap.id UnitAddCircle))

theorem cq_circleLoopClass_pairing_ne_zero :
    cohomologyEquivDualHomology ℚ (TopCat.of UnitAddCircle) 1 Singular.circleClass
      cq_circleLoopClass ≠ 0 := by
  obtain ⟨s, hs, he⟩ := spec_circleDegree_cohomologyClass_aux
  obtain ⟨c, hc⟩ := Singular.cohomologyClass_surjective (TopCat.of UnitAddCircle) 1
    Singular.circleClass
  have hp := cohomologyEquivDualHomology_cohomologyClass (TopCat.of UnitAddCircle) 1 c
    (loopCycle ℚ (ContinuousMap.id UnitAddCircle))
  rw [hc] at hp
  intro hzero
  have hv : c.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
      (loopSimplex (ContinuousMap.id UnitAddCircle))) = 0 := hp.symm.trans hzero
  have h := he c
  rw [hc, hv, mul_zero] at h
  have hunit : circleDegree Singular.circleClass = 1 := by
    have heq : Singular.circleClass = circleClassBasis 0 := by simp [circleClassBasis]
    rw [circleDegree, heq, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same]
  exact one_ne_zero (hunit.symm.trans h)

def cq_circleNormalizedLoopClass : Homology ℚ (TopCat.of UnitAddCircle) 1 :=
  (cohomologyEquivDualHomology ℚ (TopCat.of UnitAddCircle) 1 Singular.circleClass
    cq_circleLoopClass)⁻¹ • cq_circleLoopClass

theorem cq_circleNormalizedLoopClass_pairing :
    cohomologyEquivDualHomology ℚ (TopCat.of UnitAddCircle) 1 Singular.circleClass
      cq_circleNormalizedLoopClass = 1 := by
  rw [cq_circleNormalizedLoopClass, map_smul, smul_eq_mul,
    inv_mul_cancel₀ cq_circleLoopClass_pairing_ne_zero]

end HodgeLean.Foundations.Program
