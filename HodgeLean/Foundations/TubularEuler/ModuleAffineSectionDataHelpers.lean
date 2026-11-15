import HodgeLean.Foundations.TubularEuler.ModuleAffinePointPresentationHelpers
import HodgeLean.Foundations.TubularEuler.ModuleAffineFibreChartEvaluationHelpers

/-! # Actual descended module sections with the original chart equation

The section and its canonical pullback equation are retained as data constructed from the supplied module isomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

structure ModuleAffineSectionData
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N) where
  localSection : SheafOfModules.unit.{0} U.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback U.ι).obj M
  chart_equation :
    i1_module_sectionPullback hU.isoSpec.inv ((Scheme.Modules.pullback U.ι).obj M) localSection ≫ e.hom = t

def moduleAffineSectionDataOfIso
    {Q : Over (Spec (CommRingCat.of ℂ))} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N) :
    ModuleAffineSectionData M U hU N e t :=
  ⟨Classical.choose (moduleSection_iso_transport_exists hU.isoSpec.symm
      ((Scheme.Modules.pullback U.ι).obj M) N e t),
    Classical.choose_spec (moduleSection_iso_transport_exists hU.isoSpec.symm
      ((Scheme.Modules.pullback U.ι).obj M) N e t)⟩

theorem ModuleAffineSectionData.point_value
    {Q : Over (Spec (CommRingCat.of ℂ))} {M : Q.left.Modules}
    {U : Q.left.Opens} {hU : IsAffineOpen U}
    {N : (Spec (Q.left.presheaf.obj (.op U))).Modules}
    {e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N}
    {t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N}
    (d : ModuleAffineSectionData M U hU N e t)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    let b := ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr (Spec.map_preimage b).symm).hom.app N)
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map ((Scheme.Modules.pullback b).map e.hom)
        ((moduleAffinePointFibreIso M U hU x hx).hom
          (i1_moduleSectionValue M U d.localSection x hx))) =
      i1_module_pointValue N t (Spec.map (Spec.preimage b)) := by
  have h := moduleAffinePointFibreIso_section_pointPresentation M U hU d.localSection N e.hom x hx
  have ht := congrArg (fun z : SheafOfModules.unit.{0}
      (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N =>
    i1_module_pointValue N z
      (Spec.map (Spec.preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))))
    d.chart_equation
  exact h.trans ht

theorem ModuleAffineSectionData.point_value_iso
    {Q : Over (Spec (CommRingCat.of ℂ))} {M : Q.left.Modules}
    {U : Q.left.Opens} {hU : IsAffineOpen U}
    {N : (Spec (Q.left.presheaf.obj (.op U))).Modules}
    {e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N}
    {t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N}
    (d : ModuleAffineSectionData M U hU N e t)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (moduleAffineFibreChartIso M U hU N e x hx).hom
      (i1_moduleSectionValue M U d.localSection x hx) =
      i1_module_pointValue N t (Spec.map (Spec.preimage
        (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom))) := by
  exact moduleAffineFibreChartIso_apply_eq_raw M U hU N e x hx _ _ (d.point_value x hx)

#print axioms ModuleAffineSectionData.point_value_iso

#print axioms ModuleAffineSectionData.point_value

#print axioms moduleAffineSectionDataOfIso

end HodgeLean.Foundations.TubularEuler
