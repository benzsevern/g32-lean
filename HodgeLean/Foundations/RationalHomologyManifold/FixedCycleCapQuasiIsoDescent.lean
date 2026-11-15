import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleUnitCapQuasiIso
import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapAugmentedDescent
import HodgeLean.Foundations.RationalHomologyManifold.TriangulatedCohomologyComparison
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution

/-! Actual local cap descent with its quasi-isomorphism property.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual fixed-cycle cap descends through local singular cochains as a quasi-isomorphism into any degreewise injective model of its actual bounded target, retaining the original unit square and ambient homotopy.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; local cap normalization and the singular cochain resolution.
HC no distance; AV milestone no distance.
-/
theorem exists_fixedCycleCap_descent_quasiIso (X : TopCat.{0}) [T2Space X] [RegularSpace X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z (hz n))) = o.generator)
    (I : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    [∀ p, Injective (I.X p)] (j : capTargetComplex X (n + 1) ⟶ I) [QuasiIso j] :
    ∃ d : singularCochainSheafComplex ℚ X ⟶ I,
      Nonempty (Homotopy (ambientFixedCycleCapComplexHom X (n + 1) z hz ≫ j)
        (ambientCochainSheafRestriction X ≫ d)) ∧
      constantsToSingularCochainSheafComplex ℚ X ≫ d =
        ambientCupUnitComplexHom X ≫ ambientFixedCycleCapComplexHom X (n + 1) z hz ≫ j ∧
      QuasiIso d := by
  obtain ⟨d, h, hd⟩ := exists_fixedCycleCap_descent_augmented X (n + 1) z hz I j
  letI := fixedCycleUnitCap_quasiIso X n o z hz hc
  letI : QuasiIso (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
      (finiteTriangulation_contractible_basis X t)
  haveI : QuasiIso (constantsToSingularCochainSheafComplex ℚ X ≫ d) := by
    rw [hd, ← Category.assoc]
    infer_instance
  exact ⟨d, h, hd, quasiIso_of_comp_left
    (constantsToSingularCochainSheafComplex ℚ X) d⟩

#print axioms exists_fixedCycleCap_descent_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
