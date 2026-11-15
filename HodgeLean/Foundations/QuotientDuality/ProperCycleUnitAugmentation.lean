import HodgeLean.Foundations.QuotientDuality.ProperCycleCapPairing
import HodgeLean.RealDefs.FundamentalClass.Augmentation

/-! # Original cup unit and actual degree-zero augmentation
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original cup unit cochain is the actual coefficient-sum augmentation on singular zero-chains.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.2; simplicialZeroAugmentation.
HC no distance; AV milestone no distance. -/
theorem properCycle_unit_cochain_augmentation (X : TopCat.{0}) :
    unitCochain (R := ℚ) X =
      (simplicialZeroAugmentation ℚ (TopCat.toSSet.obj X)).hom := by
  rfl

/-- Evaluation by the original degree-zero cup unit is the actual singular homology augmentation.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1; HodgeLean.RealDefs.homologyπ_homology₀ε.
HC no distance; AV milestone no distance. -/
theorem properCycle_unit_pairing_augmentation (X : TopCat.{0}) :
    cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X) =
      (X.singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom := by
  let K := SingularChainComplex ℚ X
  let S := K.sc 0
  let β : LinearMap.ker S.linearDual.g.hom := ⟨unitCochain (R := ℚ) X, by
    change (((K.sc 0).f).hom.dualMap) (unitCochain (R := ℚ) X) = 0
    change ((K.d ((ComplexShape.down ℕ).prev 0) 0).hom.dualMap) (unitCochain (R := ℚ) X) = 0
    rw [ChainComplex.prev]
    exact coboundary_unitCochain X⟩
  have hu : unit (R := ℚ) X = cochainCohomologyEquiv ℚ X 0
      (S.linearDual.moduleCatHomologyClass β) := rfl
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := S.moduleCatHomologyClass_surjective z
  rw [hu]
  change S.linearDualHomologyEquiv
      ((cochainCohomologyEquiv ℚ X 0).symm
        (cochainCohomologyEquiv ℚ X 0 (S.linearDual.moduleCatHomologyClass β)))
      (S.moduleCatHomologyClass c) = _
  rw [LinearEquiv.symm_apply_apply, ShortComplex.linearDualHomologyEquiv_class_apply_class]
  let u := S.moduleCatCyclesIso.inv.hom c
  have he := ConcreteCategory.congr_hom
    (HodgeLean.RealDefs.homologyπ_homology₀ε (TopCat.toSSet.obj X)) u
  have hi : K.iCycles 0 u = c.1 := by
    change (S.moduleCatCyclesIso.inv ≫ S.iCycles).hom c = c.1
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  change (X.singularHomology₀ε (ModuleCat.of ℚ ℚ)).hom
      (S.moduleCatHomologyClass c) =
    (simplicialZeroAugmentation ℚ (TopCat.toSSet.obj X)).hom (K.iCycles 0 u) at he
  rw [hi] at he
  change unitCochain (R := ℚ) X c.1 = _
  rw [properCycle_unit_cochain_augmentation]
  exact he.symm

/-- Actual singular pushforward retains evaluation by the original degree-zero cup unit.
Source: cohomologyEquivDualHomology_cohomologyMap; HodgeLean.Foundations.Singular.cohomologyMap_unit.
HC no distance; AV milestone no distance. -/
theorem properCycle_unit_pairing_pushforward {X Y : TopCat.{0}} (f : X ⟶ Y)
    (z : Homology ℚ X 0) :
    cohomologyEquivDualHomology ℚ Y 0 (unit (R := ℚ) Y) (homologyMap ℚ 0 f z) =
      cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X) z := by
  rw [← cohomologyEquivDualHomology_cohomologyMap, cohomologyMap_unit]

end HodgeLean.Foundations.QuotientDuality
