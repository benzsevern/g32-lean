import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleUnitCapQuasiIso

/-! Monomorphy of the actual normalized unit-cap augmentation.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual normalized unit-cap augmentation is a degreewise monomorphism into the original bounded cap target.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; inclusion of the initial local orientation kernel.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleUnitCap_mono (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z (hz n))) = o.generator) :
    Mono (ambientCupUnitComplexHom X ≫ ambientFixedCycleCapComplexHom X (n + 1) z hz) := by
  let A := capTargetComplex X (n + 1)
  let k := ambientConstantsToZeroSheaf X ≫ ambientCapTargetComponent X (n + 1) z 0
  let l := A.liftCycles k 1 (CochainComplex.next ℕ 0) (fixedCycleCap_unit_cocycle X n z hz)
  letI := fixedCycleCapOrientationMap_isIso X n o z hz hc
  haveI : IsIso (l ≫ A.homologyπ 0 ≫ (capTargetInitialHomologyIso X n).hom) :=
    inferInstanceAs (IsIso (fixedCycleCapOrientationMap X n z hz))
  letI : IsIso l := IsIso.of_isIso_comp_right l
    (A.homologyπ 0 ≫ (capTargetInitialHomologyIso X n).hom)
  apply HomologicalComplex.mono_of_mono_f
  intro i
  cases i with
  | zero =>
      have hm : Mono (l ≫ A.iCycles 0) := inferInstance
      rw [HomologicalComplex.liftCycles_i] at hm
      exact hm
  | succ p =>
      exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) (p + 1) (by omega)).mono _

#print axioms fixedCycleUnitCap_mono
end HodgeLean.Foundations.RationalHomologyManifold
