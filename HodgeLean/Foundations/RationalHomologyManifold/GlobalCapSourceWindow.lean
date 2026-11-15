import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapGlobalQuasiIso

/-! The actual global cap map on the original singular short-cochain window.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Use the original reversed-dual singular short complex as the source of the actual global fixed-cycle cap window.
Source: Hatcher, Algebraic Topology, section 3.3; the standard singular cochain and cap window conventions.
HC no distance; AV milestone no distance.
-/
def globalFixedCycleCapWindow (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q + 2))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (p + q + 2) j z = 0) :
    (((SingularChainComplex ℚ X).sc (p + 1)).linearDual.map
      (forget₂ (ModuleCat ℚ) AddCommGrpCat)) ⟶
    ((((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (capTargetComplex X (p + q + 2))).sc' p (p + 1) (p + 2)) :=
  (forget₂ (ModuleCat ℚ) AddCommGrpCat).mapShortComplex.map
      (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex ℚ X) (p + 1)).inv ≫
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℕ) (p + 1)).map
      (globalFixedCycleCapComplexHom X (p + q + 2) z hz) ≫
    ((((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
      (capTargetComplex X (p + q + 2))).isoSc' p (p + 1) (p + 2)
        (CochainComplex.prev_nat_succ p) (CochainComplex.next ℕ (p + 1))).hom

#print axioms globalFixedCycleCapWindow
/-- The actual source-window identification retains the literal middle global cap component.
Source: Hatcher, Algebraic Topology, section 3.3; no change of the middle cap convention under source identification.
HC no distance; AV milestone no distance.
-/
theorem globalFixedCycleCapWindow_middle (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q + 2))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (p + q + 2) j z = 0) :
    (globalFixedCycleCapWindow X p q z hz).τ₂ =
      (globalFixedCycleCapComplexHom X (p + q + 2) z hz).f (p + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  rfl

#print axioms globalFixedCycleCapWindow_middle
/-- The actual global cap window remains a quasi-isomorphism with the original singular cochain short-complex source.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; actual global cap and canonical short-complex identifications.
HC no distance; AV milestone no distance.
-/
theorem globalFixedCycleCapWindow_quasiIso (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (p q : ℕ) (o : LocalRationalOrientation X (p + q + 2))
    (z : (SingularChainComplex ℚ X).X (p + q + 2))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (p + q + 2) j z = 0)
    (hc : localization X (p + q + 2)
      (((SingularChainComplex ℚ X).sc (p + q + 2)).moduleCatHomologyClass
        (scalarAmbientCycle X (p + q + 1) z (hz (p + q + 1)))) = o.generator) :
    ShortComplex.QuasiIso (globalFixedCycleCapWindow X p q z hz) := by
  letI := globalFixedCycleCapComplexHom_quasiIso X t (p + q + 1) o z hz hc
  haveI : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℕ) (p + 1)).map
        (globalFixedCycleCapComplexHom X (p + q + 2) z hz)) :=
    (quasiIsoAt_iff _ _).mp inferInstance
  dsimp only [globalFixedCycleCapWindow]
  infer_instance

#print axioms globalFixedCycleCapWindow_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
