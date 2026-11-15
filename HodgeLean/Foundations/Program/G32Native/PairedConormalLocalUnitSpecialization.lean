import HodgeLean.Foundations.Program.G32Native.PairedConormalRegularEvaluation
import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitComparisonForms

/-! # Canonical unit comparisons for actual local section specialization -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom

/-- Specializing a local unit section and then comparing units is the same
actual point pullback of its local unit endomorphism. -/
theorem conormal_local_unit_section_specialization {Q : Over (Spec ↧ℂ)}
    (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (SheafOfModules.unit Q.left.ringCatSheaf))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionSpecialization (SheafOfModules.unit Q.left.ringCatSheaf) U s x hx ≫
      (pullbackUnit x.left).hom =
    let a := ComplexPoint.liftToOpen Q U x hx
    (pullbackUnit a).inv ≫ (Scheme.Modules.pullback a).map
      (s ≫ (pullbackUnit U.ι).hom) ≫ (pullbackUnit a).hom := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  change (pullbackUnit a).inv ≫ (Scheme.Modules.pullback a).map s ≫
    (Scheme.Modules.pullbackComp a U.ι).hom.app (SheafOfModules.unit Q.left.ringCatSheaf) ≫
      (Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).hom.app
        (SheafOfModules.unit Q.left.ringCatSheaf) ≫ (pullbackUnit x.left).hom = _
  have hc := pullbackUnit_congr (ComplexPoint.liftToOpen_fac Q U x hx)
  change (Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).hom.app
      (SheafOfModules.unit Q.left.ringCatSheaf) ≫ (pullbackUnit x.left).hom =
    (pullbackUnit (a ≫ U.ι)).hom at hc
  have hp := pullbackUnit_composition_hom a U.ι
  change (Scheme.Modules.pullback a).map (pullbackUnit U.ι).hom ≫ (pullbackUnit a).hom =
    (Scheme.Modules.pullbackComp a U.ι).hom.app (SheafOfModules.unit Q.left.ringCatSheaf) ≫
      (pullbackUnit (a ≫ U.ι)).hom at hp
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hc, ← hp]

end HodgeLean.Foundations.Program.G32Native
