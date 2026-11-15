import HodgeLean.Foundations.Program.G32Native.ConormalIdealAmbientNaturality

/-! # Normalized ideal sections through ambient pushforward and pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

/-- The restriction comparison carries its counit to the pullback counit. -/
theorem conormalChart_restrictionPullback_counit {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.restrictFunctorAdjCounitIso f).hom.app M =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M := by
  change ((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).inv.app _ ≫
      (Scheme.Modules.restrictAdjunction f).counit.app M = _
  rw [Adjunction.leftAdjointUniq_inv_app]
  exact Adjunction.leftAdjointUniq_hom_app_counit _ _ M

/-- The original ideal section in ambient coordinates. -/
def conormalChartIdealSection {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W')
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ Conormal.idealModule j) :
    SheafOfModules.unit W'.ringCatSheaf ⟶ Conormal.idealModule (j ≫ e.hom) :=
  SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom ≫
    (Scheme.Modules.pushforward e.hom).map s ≫
      (s2e_idealModule_target_pushforward_iso j e).hom

/-- Pulling the transported ideal section back recovers the original section. -/
theorem conormalChartIdealSection_pullback {Q W W' : Scheme.{0}}
    (j : Q ⟶ W) (e : W ≅ W')
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ Conormal.idealModule j) :
    i1_module_sectionPullback e.hom (Conormal.idealModule (j ≫ e.hom))
        (conormalChartIdealSection j e s) ≫
      (conormalChartAmbientIdealIso j e).hom = s := by
  let P := Scheme.Modules.pullback e.hom
  let F := Scheme.Modules.pushforward e.hom
  let a := s2e_idealModule_target_pushforward_iso j e
  let η := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  let adj := Scheme.Modules.pullbackPushforwardAdjunction e.hom
  have hc : (Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app
      (F.obj (Conormal.idealModule j)) ≫
        (Scheme.Modules.restrictFunctorAdjCounitIso e.hom).hom.app (Conormal.idealModule j) =
      adj.counit.app (Conormal.idealModule j) := conormalChart_restrictionPullback_counit _ _
  have hn : P.map (F.map s) ≫ adj.counit.app (Conormal.idealModule j) =
      adj.counit.app (SheafOfModules.unit W.ringCatSheaf) ≫ s := adj.counit.naturality s
  have hu : P.map η ≫ adj.counit.app (SheafOfModules.unit W.ringCatSheaf) =
      (i1_module_unitPullbackIso e.hom).hom := rfl
  dsimp only [i1_module_sectionPullback, conormalChartIdealSection,
    conormalChartAmbientIdealIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  change (i1_module_unitPullbackIso e.hom).inv ≫ P.map η ≫ P.map (F.map s) ≫
    P.map a.hom ≫ P.map a.inv ≫ _ = s
  have ha : P.map a.hom ≫ P.map a.inv = 𝟙 _ := by
    rw [← P.map_comp, Iso.hom_inv_id, P.map_id]
  rw [← Category.assoc (P.map a.hom), ha, Category.id_comp]
  change (i1_module_unitPullbackIso e.hom).inv ≫ P.map η ≫ P.map (F.map s) ≫
    ((Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app
      (F.obj (Conormal.idealModule j)) ≫
        (Scheme.Modules.restrictFunctorAdjCounitIso e.hom).hom.app (Conormal.idealModule j)) = s
  rw [hc, hn, ← Category.assoc (P.map η), hu, Iso.inv_hom_id_assoc]

end HodgeLean.Foundations.TubularEuler
