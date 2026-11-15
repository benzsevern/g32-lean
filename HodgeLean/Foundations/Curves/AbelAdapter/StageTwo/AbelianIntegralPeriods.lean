import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Adapters.HolomorphicPeriodsOnX
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralLiftPairing

/-! # Integral displacement on the actual exponential cover

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.Program HodgeLean.Foundations.IntegralHomology
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- The actual exponential homomorphism is a surjective covering with its specified additive points.
Source: Birkenhake–Lange, §1.1; spec_isCoveringMap_complexExponential.
HC no distance; AV milestone no distance. -/
theorem abelianExpCover_spec :
    IsCoveringMap (complexExponentialHom A (TopologicalSpace.dim A.left)) ∧
      Function.Surjective (complexExponentialHom A (TopologicalSpace.dim A.left)) := by
  exact ⟨spec_isCoveringMap_complexExponential A _, surjective_complexExponential A _⟩

/-- Integral displacement obtained by evaluating the coordinate lift cocycles.
Source: Hatcher, §3.1; s4_c1a6_liftCocycle_pairing_cycle.
HC no distance; AV milestone no distance. -/
def abelianIntegralDisplacement :
    IntegralHomology.Lattice (TopCat.of (ComplexPoint A)) →ₗ[ℤ]
      (Fin (TopologicalSpace.dim A.left) → ℂ) :=
  LinearMap.pi fun i ↦ StageThree.cocyclePairing _
    (b3Rest2_liftCocycle (complexExponentialHom A _)
      (abelianExpCover_spec A) Additive.ofMul continuous_ofMul
      (Pi.evalAddMonoidHom _ i))

/-- On an integral cycle, the displacement is the vector of lifted endpoint differences.
Source: Hatcher, §3.1; s4_c1a6_liftCocycle_pairing_cycle.
HC no distance; AV milestone no distance. -/
theorem abelianIntegralDisplacement_cycle
    (z : (ZChains (TopCat.of (ComplexPoint A))).cycles 1) :
    abelianIntegralDisplacement A
      (Submodule.Quotient.mk ((ZChains _).homologyπ 1 z)) =
    s4_c1a6_liftChain (complexExponentialHom A _) (abelianExpCover_spec A)
      Additive.ofMul continuous_ofMul ((ZChains _).iCycles 1 z) := by
  funext i
  exact s4_c1a6_liftCocycle_pairing_cycle (complexExponentialHom A _)
    (abelianExpCover_spec A) Additive.ofMul continuous_ofMul (Pi.evalAddMonoidHom _ i) z

/-- Every integral displacement belongs to the actual exponential kernel.
Source: Birkenhake–Lange, §1.1; s4_c1a6_liftChain_cycle_project_zero.
HC no distance; AV milestone no distance. -/
theorem abelianIntegralDisplacement_mem
    (a : IntegralHomology.Lattice (TopCat.of (ComplexPoint A))) :
    abelianIntegralDisplacement A a ∈ abelianPeriodLattice A := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ZChains (TopCat.of (ComplexPoint A))).homologyπ 1)).mp inferInstance x
  rw [abelianIntegralDisplacement_cycle]
  exact s4_c1a6_liftChain_cycle_project_zero (complexExponentialHom A _)
    (abelianExpCover_spec A) Additive.ofMul continuous_ofMul z

/-- Integral homology mapped to the original exponential period lattice.
Source: Birkenhake–Lange, §1.1; abelianIntegralDisplacement_mem.
HC no distance; AV milestone no distance. -/
def abelianIntegralPeriod :
    IntegralHomology.Lattice (TopCat.of (ComplexPoint A)) →ₗ[ℤ] abelianPeriodLattice A :=
  (abelianIntegralDisplacement A).codRestrict _ (abelianIntegralDisplacement_mem A)

/-- The specified abelian lattice loop retains its original period vector.
Source: Birkenhake–Lange, §1.1; b3Rest2_liftCocycle_loop.
HC no distance; AV milestone no distance. -/
theorem abelianIntegralPeriod_loop (l : abelianPeriodLattice A) :
    abelianIntegralPeriod A (Submodule.Quotient.mk ((ZChains _).homologyπ 1
      (((ZChains _).sc 1).moduleCatCyclesIso.inv
        (loopCycle ℤ (abelianLatticeLoop A l))))) = l := by
  apply Subtype.ext
  funext i
  dsimp only [abelianIntegralPeriod, LinearMap.codRestrict_apply,
    abelianIntegralDisplacement, LinearMap.pi_apply, Subtype.coe_mk]
  change s4_c1a6_integralCocyclePairing _
    (b3Rest2_liftCocycle (complexExponentialHom A _)
      (abelianExpCover_spec A) Additive.ofMul continuous_ofMul (Pi.evalAddMonoidHom _ i)) _ = l.val i
  rw [s4_c1a6_integralCocyclePairing_cycle]
  change (b3Rest2_liftCocycle (complexExponentialHom A _)
    (abelianExpCover_spec A) Additive.ofMul continuous_ofMul (Pi.evalAddMonoidHom _ i)).val
    (s4_c1a6_zToCChainGroup _ 1
      (((((ZChains (TopCat.of (ComplexPoint A))).sc 1).moduleCatCyclesIso.inv) ≫
        ((ZChains (TopCat.of (ComplexPoint A))).sc 1).iCycles)
          (loopCycle ℤ (abelianLatticeLoop A l)))) = l.val i
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  change (b3Rest2_liftCocycle (complexExponentialHom A _)
    (abelianExpCover_spec A) Additive.ofMul continuous_ofMul (Pi.evalAddMonoidHom _ i)).val
    (s4_c1a6_zToCChainGroup _ 1
      ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) _
        (loopSimplex (abelianLatticeLoop A l))).hom (1 : ℤ))) = l.val i
  rw [s4_c1a6_zToCChainGroup_iota, Int.cast_one]
  have hh := b3Rest2_liftCocycle_loop (complexExponentialHom A _)
    (abelianExpCover_spec A) Additive.ofMul continuous_ofMul (Pi.evalAddMonoidHom _ i)
    (abelianLatticeLoop A l) (Path.segment (0 : Fin (TopologicalSpace.dim A.left) → ℂ) l.val).toContinuousMap
    (fun t ↦ congrArg Additive.ofMul
      (spec_abelianLatticeLoop_eq_complexExponential_segment A l t).symm)
  exact hh.trans (by simp)

/-- All original exponential periods occur as integral singular displacements.
Source: Birkenhake–Lange, §1.1; abelianIntegralPeriod_loop.
HC no distance; AV milestone no distance. -/
theorem abelianIntegralPeriod_surjective : Function.Surjective (abelianIntegralPeriod A) := by
  intro l
  exact ⟨_, abelianIntegralPeriod_loop A l⟩

#print axioms abelianExpCover_spec
#print axioms abelianIntegralDisplacement_cycle
#print axioms abelianIntegralDisplacement_mem
#print axioms abelianIntegralPeriod

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
