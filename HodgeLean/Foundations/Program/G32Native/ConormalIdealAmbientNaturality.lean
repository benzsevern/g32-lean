import HodgeLean.Foundations.Program.G32Native.OriginalIdealIsomorphismComparison
import HodgeLean.Foundations.BundleResolution.IdealAmbientPullbackInclusionHelpers

/-! # The ideal comparison underlying the original conormal chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution
open HodgeLean.Foundations.Algebraic

/-- The ambient ideal comparison used by the original conormal chart. -/
def conormalChartAmbientIdealIso {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W') :
    (Scheme.Modules.pullback e.hom).obj (Conormal.idealModule (j ≫ e.hom)) ≅
      Conormal.idealModule j :=
  (Scheme.Modules.pullback e.hom).mapIso
      (s2e_idealModule_target_pushforward_iso j e).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback e.hom).symm.app
      ((Scheme.Modules.pushforward e.hom).obj (Conormal.idealModule j)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app (Conormal.idealModule j)

/-- The ambient comparison retains the kernel inclusion and its unit normalization. -/
theorem conormalChartAmbientIdealIso_inclusion {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W') :
    (conormalChartAmbientIdealIso j e).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) =
      (Scheme.Modules.pullback e.hom).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ≫ e.hom).toRingCatSheafHom)) ≫
          (i1_module_unitPullbackIso e.hom).hom := by
  let P := Scheme.Modules.pullback e.hom
  let R := Scheme.Modules.restrictFunctor e.hom
  let F := Scheme.Modules.pushforward e.hom
  let N := (Scheme.Modules.restrictFunctorIsoPullback e.hom).symm
  let C := Scheme.Modules.restrictFunctorAdjCounitIso e.hom
  let A := s2e_idealModule_target_pushforward_iso j e
  let q := kernel.ι (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)
  let q' := kernel.ι (SheafOfModules.unitToPushforwardObjUnit (j ≫ e.hom).toRingCatSheafHom)
  let g := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  have hg : A.hom ≫ q' ≫ g = F.map q := by
    letI := s2e_structureModule_map_isIso e.hom
    rw [← Category.assoc, original_ideal_target_iso_inclusion j e,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hu : R.map g ≫ C.hom.app (SheafOfModules.unit W.ringCatSheaf) =
      (Scheme.Modules.restrictUnitIso e.hom).hom := i1_restrictionUnitCounit e.hom
  have hn : N.hom.app (SheafOfModules.unit W'.ringCatSheaf) ≫
      (Scheme.Modules.restrictUnitIso e.hom).hom =
        (i1_module_unitPullbackIso e.hom).hom := by
    apply (Iso.inv_comp_eq ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app
      (SheafOfModules.unit W'.ringCatSheaf))).2
    exact (f5sheaf_restrictIsoPullback_unit e.hom).symm
  change P.map A.inv ≫ N.hom.app (F.obj (Conormal.idealModule j)) ≫
    C.hom.app (Conormal.idealModule j) ≫ q = P.map q' ≫ _
  have ht := i1_transportArrow F P R N C A q q' g hg
  change P.map A.inv ≫ N.hom.app (F.obj (Conormal.idealModule j)) ≫
    C.hom.app (Conormal.idealModule j) ≫ q = P.map q' ≫ _ at ht
  exact ht.trans (by rw [hu, hn])

end HodgeLean.Foundations.TubularEuler
