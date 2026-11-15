import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapLocalOrientation
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetConcentration
import Mathlib.Algebra.Homology.SingleHomology

/-! The actual fixed-cycle unit cap as a local quasi-isomorphism.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual cap following the original cup-unit augmentation is a quasi-isomorphism when the specified cycle has the given local generators.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; local concentration and actual unit-cap normalization.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleUnitCap_quasiIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z (hz n))) = o.generator) :
    QuasiIso (ambientCupUnitComplexHom X ≫ ambientFixedCycleCapComplexHom X (n + 1) z hz) := by
  let C := TopCat.Sheaf AddCommGrpCat.{0} X
  let A := capTargetComplex X (n + 1)
  let k := ambientConstantsToZeroSheaf X ≫ ambientCapTargetComponent X (n + 1) z 0
  let l := A.liftCycles k 1 (CochainComplex.next ℕ 0) (fixedCycleCap_unit_cocycle X n z hz)
  letI := fixedCycleCapOrientationMap_isIso X n o z hz hc
  have hl : IsIso l := by
    haveI : IsIso (l ≫ A.homologyπ 0 ≫ (capTargetInitialHomologyIso X n).hom) :=
      inferInstanceAs (IsIso (fixedCycleCapOrientationMap X n z hz))
    exact IsIso.of_isIso_comp_right l (A.homologyπ 0 ≫ (capTargetInitialHomologyIso X n).hom)
  let f := ambientCupUnitComplexHom X ≫ ambientFixedCycleCapComplexHom X (n + 1) z hz
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
      rw [quasiIsoAt_iff]
      let φ := (HomologicalComplex.shortComplexFunctor C (.up ℕ) 0).map f
      let S := (CochainComplex.single₀ C).obj (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ))
      have hf : (S.sc 0).f = 0 := by
        exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ _ _
      have hg : (S.sc 0).g = 0 := by
        exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ _ _
      have hf' : (A.sc 0).f = 0 := by
        change A.d ((ComplexShape.up ℕ).prev 0) 0 = 0
        rw [CochainComplex.prev_nat_zero]
        exact A.shape 0 0 (by change ¬ (0 : ℕ) + 1 = 0; omega)
      apply (ShortComplex.quasiIso_iff_isIso_liftCycles φ hf hg hf').mpr
      change IsIso l
      exact hl
  | succ p =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact (HomologicalComplex.isZero_single_obj_homology (.up ℕ) 0
        (TopCat.Sheaf.const X (AddCommGrpCat.of ℚ)) (p + 1) (by omega)).isIso
          (capTargetComplex_homology_positive_isZero X (n + 1) o p) _

#print axioms fixedCycleUnitCap_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
