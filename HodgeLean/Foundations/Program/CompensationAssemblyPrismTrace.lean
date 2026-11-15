import HodgeLean.Foundations.Program.CompensationAssemblyPrismCupClass

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

def cq_circleLoopScalar : ℚ :=
  cohomologyEquivDualHomology ℚ (TopCat.of UnitAddCircle) 1 Singular.circleClass
    cq_circleLoopClass

theorem cq_circleLoopScalar_ne_zero : cq_circleLoopScalar ≠ 0 :=
  cq_circleLoopClass_pairing_ne_zero

theorem cq_circleLoopScalar_cocycle
    (c : Cocycle ℚ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1)
    (hc : Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 c = Singular.circleClass) :
    (cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1
      (chainOfSimplex ℚ (loopSimplex (ContinuousMap.id UnitAddCircle))) =
        cq_circleLoopScalar := by
  have h := cohomologyEquivDualHomology_cohomologyClass (TopCat.of UnitAddCircle) 1
    (cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c)
    (loopCycle ℚ (ContinuousMap.id UnitAddCircle))
  rw [cq_normalizedCocycle_class, hc] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_eq_signed_trace (X : TopCat.{0}) (n : ℕ)
    (b : Cohomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1)) :
    cq_circleCohomologyPrism X n b =
      -((-1 : ℤ) ^ n • (cq_circleLoopScalar • cq_circleTrace X n b)) := by
  obtain ⟨c, hc⟩ := Singular.cohomologyClass_surjective (TopCat.of UnitAddCircle) 1
    Singular.circleClass
  obtain ⟨⟨u, v⟩, rfl⟩ := (Singular.prodCircleCohomologyEquiv X n).surjective b
  have ht : cq_circleTrace X n (Singular.prodCircleCohomologyEquiv X n (u, v)) = v := by
    change ((Singular.prodCircleCohomologyEquiv X n).symm
      (Singular.prodCircleCohomologyEquiv X n (u, v))).2 = v
    rw [LinearEquiv.symm_apply_apply]
  rw [ht, Singular.prodCircleCohomologyEquiv_apply, map_add,
    cq_circleCohomologyPrism_pullback, zero_add]
  have h := cq_circlePrism_cup_class X n v c
  rw [hc, cq_circleLoopScalar_cocycle c hc] at h
  exact h

def cq_circlePrismFactor (n : ℕ) : ℚ := -((-1 : ℚ) ^ n * cq_circleLoopScalar)

theorem cq_circlePrismFactor_ne_zero (n : ℕ) : cq_circlePrismFactor n ≠ 0 := by
  exact neg_ne_zero.mpr (mul_ne_zero
    (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) cq_circleLoopScalar_ne_zero)

theorem cq_circlePrism_signed_smul (n : ℕ) {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : V) : -((-1 : ℤ) ^ n • (cq_circleLoopScalar • v)) = cq_circlePrismFactor n • v := by
  rw [← Int.cast_smul_eq_zsmul ℚ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, smul_smul, ← neg_smul]
  rfl

theorem cq_circlePrism_eq_factor_trace (X : TopCat.{0}) (n : ℕ)
    (b : Cohomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1)) :
    cq_circleCohomologyPrism X n b = cq_circlePrismFactor n • cq_circleTrace X n b :=
  (cq_circlePrism_eq_signed_trace X n b).trans (cq_circlePrism_signed_smul n _)

end HodgeLean.Foundations.Program
