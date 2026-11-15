import HodgeLean.Foundations.Program.G32Native.ConormalIdealSectionNaturality
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalIsoHelpers

/-! # Sections of the conormal through source and ambient isomorphisms -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

/-- Normalized section pullback respects a morphism of module sheaves. -/
theorem conormalSection_pullback_map {X Y : Scheme.{0}} (f : X ⟶ Y)
    {M N : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (q : M ⟶ N) :
    i1_module_sectionPullback f N (s ≫ q) =
      i1_module_sectionPullback f M s ≫ (Scheme.Modules.pullback f).map q := by
  simp only [i1_module_sectionPullback, Functor.map_comp, Category.assoc]

/-- The source comparison transports the pullback of the same ideal section. -/
theorem conormalSection_source_iso {Q Q' W : Scheme.{0}}
    (j : Q ⟶ W) (e : Q' ≅ Q)
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ Conormal.idealModule j) :
    i1_module_sectionPullback e.hom (Conormal.sheaf j)
        (i1_module_sectionPullback j (Conormal.idealModule j) s) ≫
      (s2e_conormal_source_iso j e).hom =
    i1_module_sectionPullback (e.hom ≫ j) (Conormal.idealModule (e.hom ≫ j))
      (s ≫ (s2e_idealModule_source_iso j e).hom) := by
  dsimp only [s2e_conormal_source_iso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  erw [← i1_module_sectionPullback_comp, conormalSection_pullback_map]

/-- An ambient comparison transports conormal sections whenever it transports
 their ideal sections. -/
theorem conormalSection_target_iso {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W')
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ Conormal.idealModule j)
    (t : SheafOfModules.unit W'.ringCatSheaf ⟶ Conormal.idealModule (j ≫ e.hom))
    (ht : i1_module_sectionPullback e.hom (Conormal.idealModule (j ≫ e.hom)) t ≫
      (conormalChartAmbientIdealIso j e).hom = s) :
    i1_module_sectionPullback (j ≫ e.hom) (Conormal.idealModule (j ≫ e.hom)) t ≫
      (s2e_conormal_target_iso j e).hom =
        i1_module_sectionPullback j (Conormal.idealModule j) s := by
  rw [i1_module_sectionPullback_comp]
  change (_ ≫ (Scheme.Modules.pullbackComp j e.hom).hom.app
      (Conormal.idealModule (j ≫ e.hom))) ≫
    ((Scheme.Modules.pullbackComp j e.hom).inv.app (Conormal.idealModule (j ≫ e.hom)) ≫
      (Scheme.Modules.pullback j).map (conormalChartAmbientIdealIso j e).hom) = _
  rw [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← conormalSection_pullback_map, ht]

end HodgeLean.Foundations.TubularEuler
