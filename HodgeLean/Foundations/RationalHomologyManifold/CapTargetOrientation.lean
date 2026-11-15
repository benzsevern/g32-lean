import HodgeLean.Foundations.RationalHomologyManifold.CapTargetInitialHomology
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionDerivedOrientation

/-! The original rational orientation on actual initial cap-target homology.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Transport the original local orientation through the actual stage-zero subdivision map and the initial bounded cap homology identification.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; normalized local chain orientation.
HC no distance; AV milestone no distance.
-/
def capTargetOrientationHomologyIso (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1)) :
    (capTargetComplex X (n + 1)).homology 0 ≅ TopCat.Sheaf.const X (AddCommGrpCat.of ℚ) := by
  letI := subdivisionSheafStage_quasiIso X 0
  exact capTargetInitialHomologyIso X n ≪≫
    (asIso (HomologicalComplex.homologyMap (subdivisionSheafStage X 0) (n + 1))).symm ≪≫
      (localOrientationHomologySheafIso X (n + 1) o).symm

#print axioms capTargetOrientationHomologyIso
/-- The cap-target orientation retains the original local orientation under the actual stage-zero homology map.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; orientation normalization under subdivision.
HC no distance; AV milestone no distance.
-/
theorem capTargetOrientationHomologyIso_stage (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X (n + 1)) :
    HomologicalComplex.homologyMap (subdivisionSheafStage X 0) (n + 1) ≫
      (capTargetInitialHomologyIso X n).inv ≫ (capTargetOrientationHomologyIso X n o).hom =
        (localOrientationHomologySheafIso X (n + 1) o).inv := by
  letI := subdivisionSheafStage_quasiIso X 0
  dsimp only [capTargetOrientationHomologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    Iso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]

#print axioms capTargetOrientationHomologyIso_stage
end HodgeLean.Foundations.RationalHomologyManifold
