import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLimitHomology
import HodgeLean.Foundations.QuotientDuality.LocalOrientationDerived
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! The actual subdivision-limit complex in cohomological grading and its orientation comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Regrade the actual supported subdivision-limit complex by placing chain degree `n` in cohomological degree `-n`.
Source: Bredon, Sheaf Theory, second edition, VI.12; the cohomological supported-chain convention.
HC no distance; AV milestone no distance.
-/
def subdivisionLimitSheafCochainComplex (X : TopCat.{0}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  (subdivisionLimitSheafComplex X).extend ComplexShape.embeddingDownNat

#print axioms subdivisionLimitSheafCochainComplex
/-- The actual finite-stage subdivision comparison in cohomological grading.
Source: Bredon, Sheaf Theory, second edition, VI.12; the supported-chain subdivision comparison.
HC no distance; AV milestone no distance.
-/
def subdivisionSheafCochainStage (X : TopCat.{0}) (m : ℕ) :
    singularChainSheafCochainComplex ℚ X ⟶ subdivisionLimitSheafCochainComplex X :=
  HomologicalComplex.extendMap (subdivisionSheafStage X m) ComplexShape.embeddingDownNat

#print axioms subdivisionSheafCochainStage
/-- Regrading retains the actual finite-stage quasi-isomorphism.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision invariance with cohomological grading.
HC no distance; AV milestone no distance.
-/
theorem subdivisionSheafCochainStage_quasiIso (X : TopCat.{0}) (m : ℕ) :
    QuasiIso (subdivisionSheafCochainStage X m) := by
  letI := subdivisionSheafStage_quasiIso X m
  exact inferInstanceAs (QuasiIso
    (HomologicalComplex.extendMap (subdivisionSheafStage X m) ComplexShape.embeddingDownNat))

#print axioms subdivisionSheafCochainStage_quasiIso
/-- Local orientation concentration holds for the actual cohomologically regraded subdivision-limit sheaf.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; local homology concentration and subdivision.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheafCochainHomology_concentrated (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (i : ℤ) (hi : i ≠ -(n : ℤ)) :
    IsZero ((subdivisionLimitSheafCochainComplex X).homology i) := by
  letI := subdivisionSheafCochainStage_quasiIso X 0
  apply (asIso (HomologicalComplex.homologyMap (subdivisionSheafCochainStage X 0) i)).isZero_iff.mp
  exact singularChainSheafCochainHomology_concentrated ℚ X n
    (fun m hm x => by
      letI := o.vanishes x m hm
      exact ModuleCat.isZero_of_subsingleton _) i hi

#print axioms subdivisionLimitSheafCochainHomology_concentrated
/-- Use the standard localization category for the actual sheaf complexes.
Source: Mathlib, Algebra.Homology.DerivedCategory.Basic, HasDerivedCategory.standard.
HC no distance; AV milestone no distance.
-/
local instance subdivisionDerivedCategory (X : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _

/-- Transport the existing normalized local orientation through the actual stage-zero subdivision comparison.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; the oriented local singular-chain model.
HC no distance; AV milestone no distance.
-/
def subdivisionDerivedSingleOrientationIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X n) :
    DerivedCategory.Q.obj (subdivisionLimitSheafCochainComplex X) ≅
      (DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) (-(n : ℤ))).obj
        𝓒(X; ℚ) := by
  letI := subdivisionSheafCochainStage_quasiIso X 0
  exact (asIso (DerivedCategory.Q.map (subdivisionSheafCochainStage X 0))).symm ≪≫
    localOrientationDerivedSingleIso X n o

#print axioms subdivisionDerivedSingleOrientationIso
/-- The transported derived orientation retains the actual stage-zero comparison with the original orientation.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; normalization under subdivision.
HC no distance; AV milestone no distance.
-/
theorem subdivisionDerivedSingleOrientationIso_stage (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) :
    DerivedCategory.Q.map (subdivisionSheafCochainStage X 0) ≫
      (subdivisionDerivedSingleOrientationIso X n o).hom =
        (localOrientationDerivedSingleIso X n o).hom := by
  letI := subdivisionSheafCochainStage_quasiIso X 0
  simp [subdivisionDerivedSingleOrientationIso]

#print axioms subdivisionDerivedSingleOrientationIso_stage
/-- The actual surviving homology of the subdivision-limit complex carries the original local orientation through the stage-zero map.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; oriented local homology under subdivision.
HC no distance; AV milestone no distance.
-/
def subdivisionOrientationHomologyIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X n) :
    (subdivisionLimitSheafCochainComplex X).homology (-(n : ℤ)) ≅ 𝓒(X; ℚ) := by
  letI := subdivisionSheafCochainStage_quasiIso X 0
  exact (asIso (HomologicalComplex.homologyMap (subdivisionSheafCochainStage X 0) (-(n : ℤ)))).symm ≪≫
    singularChainSheafCochainHomologyIso ℚ X n ≪≫ (localOrientationHomologySheafIso X n o).symm

#print axioms subdivisionOrientationHomologyIso
/-- The surviving homology orientation is normalized by the actual stage-zero homology map.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; normalization of the local homology generator.
HC no distance; AV milestone no distance.
-/
theorem subdivisionOrientationHomologyIso_stage (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) :
    HomologicalComplex.homologyMap (subdivisionSheafCochainStage X 0) (-(n : ℤ)) ≫
      (subdivisionOrientationHomologyIso X n o).hom =
        (singularChainSheafCochainHomologyIso ℚ X n).hom ≫
          (localOrientationHomologySheafIso X n o).inv := by
  letI := subdivisionSheafCochainStage_quasiIso X 0
  simp [subdivisionOrientationHomologyIso]

#print axioms subdivisionOrientationHomologyIso_stage
/-- The actual subdivision-limit localization defines a cohomologically bounded-below derived object by local orientation concentration.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; the oriented chain-sheaf object.
HC no distance; AV milestone no distance.
-/
def subdivisionLimitSheafPlusObject (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X n) :
    DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  DerivedCategory.concentratedPlusObject (subdivisionLimitSheafCochainComplex X) (-(n : ℤ))
    (subdivisionLimitSheafCochainHomology_concentrated X n o)

#print axioms subdivisionLimitSheafPlusObject
/-- The bounded-below derived object is literally the localization of the actual subdivision-limit complex.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; the actual oriented chain-sheaf object.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheafPlusObject_obj (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X n) :
    DerivedCategory.Plus.ι.obj (subdivisionLimitSheafPlusObject X n o) =
      DerivedCategory.Q.obj (subdivisionLimitSheafCochainComplex X) := rfl

#print axioms subdivisionLimitSheafPlusObject_obj
end HodgeLean.Foundations.RationalHomologyManifold
