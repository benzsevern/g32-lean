import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleUnitCapMono
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenInjectiveResolution

/-! An actual injective comparison of the original bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Extend the actual normalized unit-cap augmentation to the existing constant rational injective resolution.
Source: Bredon, Sheaf Theory, second edition, II.4 and VI.12; injective extension along the actual unit-cap monomorphism.
HC no distance; AV milestone no distance.
-/
def fixedCycleCapInjectiveMap (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z (hz n))) = o.generator) :
    capTargetComplex X (n + 1) ⟶
      (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).cocomplex := by
  letI := fixedCycleUnitCap_quasiIso X n o z hz hc
  letI := fixedCycleUnitCap_mono X n o z hz hc
  exact CochainComplex.liftToInjectiveNat
    (ambientCupUnitComplexHom X ≫ ambientFixedCycleCapComplexHom X (n + 1) z hz)
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective

#print axioms fixedCycleCapInjectiveMap
/-- The actual bounded target comparison with the existing injective resolution is a quasi-isomorphism.
Source: Bredon, Sheaf Theory, second edition, II.4 and VI.12; the actual normalized unit augmentation comparison.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapInjectiveMap_quasiIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z (hz n))) = o.generator) :
    QuasiIso (fixedCycleCapInjectiveMap X n o z hz hc) := by
  letI := fixedCycleUnitCap_quasiIso X n o z hz hc
  letI := fixedCycleUnitCap_mono X n o z hz hc
  exact CochainComplex.liftToInjectiveNat_quasiIso _ _ _

#print axioms fixedCycleCapInjectiveMap_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
