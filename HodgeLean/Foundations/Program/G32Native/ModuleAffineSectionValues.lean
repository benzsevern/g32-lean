import HodgeLean.Foundations.TubularEuler.ModuleAffineSectionDataHelpers
import HodgeLean.Foundations.TubularEuler.ModuleSectionIsoDescentHelpers

/-! # Uniqueness and specialization of actual descended module sections -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

/-- The original chart equation fixes the descended section uniquely.
Source: `moduleSectionPullback_iso_bijective` and cancellation of an isomorphism.
HC no distance; AV milestone no distance. -/
theorem ModuleAffineSectionData.localSection_unique
    {Q : Over (Spec ↧ℂ)} {M : Q.left.Modules}
    {U : Q.left.Opens} {hU : IsAffineOpen U}
    {N : (Spec (Q.left.presheaf.obj (.op U))).Modules}
    {e : (Scheme.Modules.pullback hU.isoSpec.inv).obj
      ((Scheme.Modules.pullback U.ι).obj M) ≅ N}
    {t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N}
    (d d' : ModuleAffineSectionData M U hU N e t) :
    d.localSection = d'.localSection := by
  apply (moduleSectionPullback_iso_bijective hU.isoSpec.symm
    ((Scheme.Modules.pullback U.ι).obj M)).1
  apply (cancel_mono e.hom).1
  exact d.chart_equation.trans d'.chart_equation.symm

#print axioms ModuleAffineSectionData.localSection_unique

/-- Specialization of a descended section followed by a specified fibre
isomorphism retains the supplied value of the original chart section.
Source: `ModuleAffineSectionData.point_value_iso` and evaluation of a
composite module homomorphism.
HC no distance; AV milestone no distance. -/
theorem ModuleAffineSectionData.point_value_composite
    {Q : Over (Spec ↧ℂ)} {M : Q.left.Modules}
    {U : Q.left.Opens} {hU : IsAffineOpen U}
    {N : (Spec (Q.left.presheaf.obj (.op U))).Modules}
    {e : (Scheme.Modules.pullback hU.isoSpec.inv).obj
      ((Scheme.Modules.pullback U.ι).obj M) ≅ N}
    {t : SheafOfModules.unit.{0} (Spec (Q.left.presheaf.obj (.op U))).ringCatSheaf ⟶ N}
    (d : ModuleAffineSectionData M U hU N e t)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    let b := ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom
    ∀ {T : ModuleCat ℂ}
      (a : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback (Spec.map (Spec.preimage b))).obj N) ≅ T)
      (y : T),
      a.hom (i1_module_pointValue N t (Spec.map (Spec.preimage b))) = y →
      ((moduleAffineFibreChartIso M U hU N e x hx) ≪≫ a).hom
        (i1_moduleSectionValue M U d.localSection x hx) = y := by
  intro b T a y hy
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [d.point_value_iso x hx]
  exact hy

#print axioms ModuleAffineSectionData.point_value_composite

end HodgeLean.Foundations.TubularEuler
