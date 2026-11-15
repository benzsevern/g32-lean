import HodgeLean.Foundations.Program.G32Native.PairedConormalPointCoordinatesProjection
import HodgeLean.Foundations.BundleThom.ConormalFrameCoefficientHelpers
import HodgeLean.Foundations.BundleThom.ConormalFrameRestrictionHelpers
import HodgeLean.Foundations.BundleThom.ConormalSectionAlgebraHelpers
import HodgeLean.Foundations.BundleThom.DualCoordinateEvaluationHelpers
import HodgeLean.Foundations.BundleThom.FreePointProjectionHelpers
import HodgeLean.Foundations.BundleThom.FreeSectionSpecializationHelpers
import HodgeLean.Foundations.BundleThom.InverseFrameContinuityHelpers
import HodgeLean.Foundations.BundleThom.InverseFrameEvaluationHelpers
import HodgeLean.Foundations.BundleThom.LocalSectionRestrictionHelpers
import HodgeLean.Foundations.BundleThom.ModuleSectionPullbackHelpers
import HodgeLean.Foundations.BundleThom.ModuleSectionTransportHelpers
import HodgeLean.Foundations.BundleThom.UnitCompositionHelpers
import HodgeLean.Foundations.BundleThom.UnitSpecializationHelpers
/-! # Literal scalar rows of actual presentation fibre coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- Each canonical free coordinate is the scalar of the same actual pulled row. -/
theorem conormal_unit_free_fibre_coordinate_row {X : Scheme.{0}}
    (x : Spec (CommRingCat.of ℂ) ⟶ X) (k : ℕ)
    (z : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x).obj
        (SheafOfModules.unit X.ringCatSheaf ⊞
          SheafOfModules.free (R := X.ringCatSheaf) (Fin k)))) (i : Fin k) :
    (conormalUnitFreeFibreCoordinates x k z).2 i =
      i1_unitPointCoordinates
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          ((Scheme.Modules.pullback x).map
            ((biprod.snd : (SheafOfModules.unit X.ringCatSheaf ⊞
              SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ⟶
              SheafOfModules.free (R := X.ringCatSheaf) (Fin k)) ≫
                i1_freeSheafProjection X k i) ≫
            (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom) z) := by
  rw [conormal_unit_free_fibre_coordinate_snd, i1_freePointCoordinates_projection,
    i1_unitPointCoordinates_apply]
  let F := Scheme.Modules.pullback x
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let A := SheafOfModules.unit X.ringCatSheaf
  let B := SheafOfModules.free (R := X.ringCatSheaf) (Fin k)
  have hc : F.map (biprod.snd : A ⊞ B ⟶ B) ≫
      (SheafOfModules.pullbackObjFreeIso x.toRingCatSheafHom (Fin k)).hom ≫
        i1_freeSheafProjection (Spec ↧ℂ) k i =
      F.map ((biprod.snd : A ⊞ B ⟶ B) ≫ i1_freeSheafProjection X k i) ≫
        (HodgeLean.Foundations.Curves.Picard.LineBundles.pullbackUnit x).hom := by
    rw [← i1_freeSheafProjection_pullback x k i]
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    rfl
  have hz := congrArg (fun f => (G.map f) z) hc
  simp only [CategoryTheory.Functor.map_comp] at hz
  convert! congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom hz using 1
  all_goals simp only [G, F, CategoryTheory.Functor.map_comp]
  all_goals rfl

end HodgeLean.Foundations.Program.G32Native
