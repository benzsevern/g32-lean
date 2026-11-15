import HodgeLean.Foundations.Program.G32Native.PairedConormalPointSectionValues
import HodgeLean.Foundations.Program.G32Native.PairedConormalPointCoordinatesProjection
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveScheme

/-! # Ordered actual generator values of an elementary presentation -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The actual ordered generators, with the distinguished unit coordinate first. -/
def conormalPresentationGenerator (X : Scheme.{0}) (k : ℕ) (r : Fin (k + 1)) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (SheafOfModules.unit X.ringCatSheaf ⊞
        SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) :=
  Fin.cases biprod.inl (fun i => SheafOfModules.ιFree i ≫ biprod.inr) r

/-- The distinguished actual generator has exactly the leading standard
coordinate in the canonical point-fibre comparison. -/
theorem conormal_point_generator_inl {X : Scheme.{0}} (x : Spec ↧ℂ ⟶ X) (k : ℕ) :
    conormalUnitFreeFibreCoordinates x k
      (pairedPointSectionValue
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) biprod.inl x) = (1, 0) := by
  let P := SheafOfModules.unit X.ringCatSheaf ⊞
    SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  apply Prod.ext
  · rw [conormal_unit_free_fibre_coordinate_fst]
    rw [← paired_pointSectionValue_naturality
      (biprod.fst : P ⟶ SheafOfModules.unit X.ringCatSheaf) biprod.inl x,
      biprod.inl_fst]
    exact paired_pointSectionValue_unit x
  · rw [conormal_unit_free_fibre_coordinate_snd]
    rw [← paired_pointSectionValue_naturality
      (biprod.snd : P ⟶ SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) biprod.inl x,
      biprod.inl_snd, paired_pointSectionValue_zero, map_zero, map_zero]

/-- Every trailing actual generator retains its standard free coordinate. -/
theorem conormal_point_generator_inr {X : Scheme.{0}} (x : Spec ↧ℂ ⟶ X)
    (k : ℕ) (i : Fin k) :
    conormalUnitFreeFibreCoordinates x k
      (pairedPointSectionValue
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
        (SheafOfModules.ιFree i ≫ biprod.inr) x) = (0, Pi.single i 1) := by
  let P := SheafOfModules.unit X.ringCatSheaf ⊞
    SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  apply Prod.ext
  · rw [conormal_unit_free_fibre_coordinate_fst]
    rw [← paired_pointSectionValue_naturality
      (biprod.fst : P ⟶ SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.ιFree i ≫ biprod.inr) x,
      Category.assoc, biprod.inr_fst, comp_zero,
      paired_pointSectionValue_zero, map_zero, map_zero]
  · rw [conormal_unit_free_fibre_coordinate_snd]
    rw [← paired_pointSectionValue_naturality
      (biprod.snd : P ⟶ SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
      (SheafOfModules.ιFree i ≫ biprod.inr) x,
      Category.assoc, biprod.inr_snd, Category.comp_id]
    exact paired_pointSectionValue_free_generator x k i

/-- The actual ordered generators become the literal ordered homogeneous basis. -/
theorem conormal_point_generator_coordinates {X : Scheme.{0}} (x : Spec ↧ℂ ⟶ X)
    (k : ℕ) (r : Fin (k + 1)) :
    conormalUnitFreeFibreCoordinates x k
      (pairedPointSectionValue
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k))
        (conormalPresentationGenerator X k r) x) =
      (EulerModel.normalHomogeneousCoordinates k).symm (Pi.single r 1) := by
  induction r using Fin.cases with
  | zero =>
    rw [conormalPresentationGenerator, Fin.cases_zero, conormal_point_generator_inl]
    apply Prod.ext
    · simp [EulerModel.normalHomogeneousCoordinates]
    · funext i
      simp [EulerModel.normalHomogeneousCoordinates, Pi.single_apply]
  | succ i =>
    rw [conormalPresentationGenerator, Fin.cases_succ, conormal_point_generator_inr]
    apply Prod.ext
    · simp [EulerModel.normalHomogeneousCoordinates, Pi.single_apply]
    · funext j
      simp [EulerModel.normalHomogeneousCoordinates, Pi.single_apply, Fin.succ_inj]

#print axioms conormal_point_generator_coordinates
#print axioms conormal_point_generator_inr
#print axioms conormal_point_generator_inl
end HodgeLean.Foundations.Program.G32Native
