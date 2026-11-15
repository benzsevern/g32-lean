import HodgeLean.Foundations.BundleResolution.ModuleSectionHelpers
import HodgeLean.Foundations.Algebraic.GrassmannianSheafPullback

/-! # Normalized pullback of unit-valued module sections

The canonical unit comparison identifies the pullback of the structure
module with the structure module and therefore pulls back actual sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution

def i1_module_unitPullbackIso {X Y : Scheme.{0}} (f : X ⟶ Y) :
    CategoryTheory.Iso (C := SheafOfModules X.ringCatSheaf)
      ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf))
      (SheafOfModules.unit X.ringCatSheaf) := by
  letI : (SheafOfModules.pushforward.{0} f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  exact asIso (C := SheafOfModules X.ringCatSheaf)
    (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom)

def i1_module_sectionPullback {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj M :=
  (i1_module_unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s
end HodgeLean.Foundations.BundleResolution
