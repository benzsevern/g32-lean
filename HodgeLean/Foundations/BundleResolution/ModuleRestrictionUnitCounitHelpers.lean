import HodgeLean.Foundations.BundleResolution.ModuleUnitPullbackHelpers

/-! # The actual restriction counit on the structure module

The structure-module arrow and the restriction counit retain the unit.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open HodgeLean.Foundations.Algebraic
namespace HodgeLean.Foundations.BundleResolution

theorem i1_restrictionUnitCounit {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).map
      (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
      (Scheme.Modules.restrictFunctorAdjCounitIso j).hom.app
        (SheafOfModules.unit X.ringCatSheaf) =
    (Scheme.Modules.restrictUnitIso j).hom := by
  apply (cancel_epi (Scheme.Modules.restrictUnitIso j).inv).1
  apply f5sheaf_unit_hom_ext
  intro U
  change X.presheaf.map _
    (j.app (j ''ᵁ U.unop) ((j.appIso U.unop).inv (1 : Γ(X, U.unop)))) =
    (j.appIso U.unop).hom ((j.appIso U.unop).inv (1 : Γ(X, U.unop)))
  simp only [map_one]

end HodgeLean.Foundations.BundleResolution
