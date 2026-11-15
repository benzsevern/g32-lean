import HodgeLean.Foundations.BundleResolution.IdealAmbientPushforwardInclusionHelpers
import HodgeLean.Foundations.BundleResolution.ModuleRestrictionUnitCounitHelpers
import HodgeLean.Foundations.BundleResolution.ModuleTransportArrowHelpers

/-! # Ambient inverse-image transport retains the actual ideal inclusion

The unit comparison fixes the normalization of the transported kernel arrow.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program HodgeLean.Foundations.Algebraic
namespace HodgeLean.Foundations.BundleResolution

theorem i1_ambientIsoIdealPullbackIso_inclusion {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsIso j] :
    (s2e_ambientIsoIdealPullbackIso f j).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
    (Scheme.Modules.pullback j).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (f ≫ j).toRingCatSheafHom)) ≫
      (i1_module_unitPullbackIso j).hom := by
  let P := Scheme.Modules.pullback j
  let R := Scheme.Modules.restrictFunctor j
  let F := Scheme.Modules.pushforward j
  let N := (Scheme.Modules.restrictFunctorIsoPullback j).symm
  let C := Scheme.Modules.restrictFunctorAdjCounitIso j
  let A := s2e_ambientIsoIdealPushforwardIso f j
  let q := kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  let q' := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (f ≫ j).toRingCatSheafHom)
  let g := SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom
  have hg : A.hom ≫ q' ≫ g = F.map q :=
    i1_ambientIsoIdealPushforwardIso_inclusion f j
  have hu : R.map g ≫ C.hom.app (SheafOfModules.unit Y.ringCatSheaf) =
      (Scheme.Modules.restrictUnitIso j).hom := i1_restrictionUnitCounit j
  have hn : N.hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.restrictUnitIso j).hom = (i1_module_unitPullbackIso j).hom := by
    apply (Iso.inv_comp_eq ((Scheme.Modules.restrictFunctorIsoPullback j).app
      (SheafOfModules.unit Z.ringCatSheaf))).2
    exact (f5sheaf_restrictIsoPullback_unit j).symm
  change P.map A.inv ≫ N.hom.app (F.obj (s2c_idealModule f)) ≫
    C.hom.app (s2c_idealModule f) ≫ q = P.map q' ≫ _
  have ht := i1_transportArrow F P R N C A q q' g hg
  change P.map A.inv ≫ N.hom.app (F.obj (s2c_idealModule f)) ≫
    C.hom.app (s2c_idealModule f) ≫ q = P.map q' ≫ _ at ht
  exact ht.trans (by rw [hu, hn])

end HodgeLean.Foundations.BundleResolution
