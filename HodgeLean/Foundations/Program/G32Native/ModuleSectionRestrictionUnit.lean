import HodgeLean.Foundations.Program.G32Native.ModuleSectionRestriction

/-! # Original structure-module coefficients in local section restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction of a section of the original structure module has the
actual pulled-back original coefficient with the specified unit comparisons. -/
theorem moduleSectionRestrict_structure {W : Scheme.{0}}
    (U V : W.Opens) (hVU : V ≤ U)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (unit W)) :
    moduleSectionRestrict (unit W) U V hVU s ≫ (pullbackUnit V.ι).hom =
    (pullbackUnit (W.homOfLE hVU)).inv ≫
      (Scheme.Modules.pullback (W.homOfLE hVU)).map (s ≫ (pullbackUnit U.ι).hom) ≫
      (pullbackUnit (W.homOfLE hVU)).hom := by
  let j := W.homOfLE hVU
  let hk := W.homOfLE_ι hVU
  let C := Scheme.Modules.pullbackComp j U.ι
  let D := Scheme.Modules.pullbackCongr hk
  have hu : (C.app (unit W)).hom ≫ (D.app (unit W)).hom ≫ (pullbackUnit V.ι).hom =
      (Scheme.Modules.pullback j).map (pullbackUnit U.ι).hom ≫ (pullbackUnit j).hom := by
    rw [pullbackUnit_congr hk]
    exact (pullbackUnit_composition_hom j U.ι).symm
  change (pullbackUnit j).inv ≫ (Scheme.Modules.pullback j).map s ≫
    (C.app (unit W)).hom ≫ (D.app (unit W)).hom ≫ (pullbackUnit V.ι).hom = _
  rw [hu]
  simp only [Functor.map_comp, Category.assoc]
  rfl

#print axioms moduleSectionRestrict_structure
end HodgeLean.Foundations.Program.G32Native
