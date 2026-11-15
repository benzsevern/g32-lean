import HodgeLean.Foundations.BundleThom.UnitSpecializationHelpers
import HodgeLean.Foundations.BundleThom.ModuleSectionPullbackHelpers

/-! # The canonical pullback square for arbitrary module sections

The specified section and point morphism remain unchanged through the module pullback unit.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

theorem moduleSection_pullback_unit_square {S T : Scheme.{0}} (a : S ⟶ T)
    (M : T.Modules) (s : SheafOfModules.unit.{0} T.ringCatSheaf ⟶ M) :
    letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
    letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
    let u := SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
    letI : IsIso u := inferInstanceAs (IsIso
      (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map a.base)
        a.toRingCatSheafHom))
    SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward a).map (inv u ≫ (Scheme.Modules.pullback a).map s) =
        s ≫ (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M := by
  letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let F := Scheme.Modules.pullback a
  let G := Scheme.Modules.pushforward a
  let adj := SheafOfModules.pullbackPushforwardAdjunction a.toRingCatSheafHom
  let u := SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map a.base)
      a.toRingCatSheafHom))
  let v := SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom
  let h := inv u ≫ F.map s
  have hc : u ≫ h = F.map s := by simp only [h, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hu : adj.homEquiv _ _ u = v :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  calc
    v ≫ G.map h = adj.homEquiv _ _ (u ≫ h) := by
      rw [adj.homEquiv_naturality_right, hu]
      rfl
    _ = adj.homEquiv _ _ (F.map s) := congrArg (adj.homEquiv _ _) hc
    _ = s ≫ adj.unit.app M := by
      rw [Adjunction.homEquiv_unit]
      exact (adj.unit.naturality s).symm

#print axioms moduleSection_pullback_unit_square

theorem moduleSection_pullback_top_value {S T : Scheme.{0}} (a : S ⟶ T)
    (M : T.Modules) (s : SheafOfModules.unit.{0} T.ringCatSheaf ⟶ M) :
    (HodgeLean.Foundations.BundleThom.i1_moduleSectionPullback a M s).val.app (.op ⊤)
        (1 : Γ(S, ⊤)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).val.app (.op ⊤)
        (s.val.app (.op ⊤) (1 : Γ(T, ⊤))) := by
  let h := HodgeLean.Foundations.BundleThom.i1_moduleSectionPullback a M s
  let G := Scheme.Modules.pushforward a
  let η := (Scheme.Modules.pullbackPushforwardAdjunction a).unit
  have hs : SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom ≫ G.map h =
      s ≫ η.app M := moduleSection_pullback_unit_square a M s
  have hev := congrArg (fun f : SheafOfModules.unit.{0} T.ringCatSheaf ⟶
      G.obj ((Scheme.Modules.pullback a).obj M) =>
      (f.val.app (.op ⊤)).hom (1 : Γ(T, ⊤))) hs
  change (h.val.app (.op ⊤)).hom ((a.app ⊤) (1 : Γ(T, ⊤))) =
    ((η.app M).val.app (.op ⊤)).hom (s.val.app (.op ⊤) (1 : Γ(T, ⊤))) at hev
  rw [map_one] at hev
  exact hev

#print axioms moduleSection_pullback_top_value

end HodgeLean.Foundations.TubularEuler
