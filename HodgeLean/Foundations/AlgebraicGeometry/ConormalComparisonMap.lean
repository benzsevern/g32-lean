import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs
import HodgeLean.Foundations.Program.SchoenCycleC2UnitCompositionHelpers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Natural maps for conormal comparison
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program

namespace AlgebraicGeometry.Conormal

lemma structureMap_congr {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) :
    SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom ≫
      eqToHom (congrArg (fun t : X ⟶ Y =>
        (Scheme.Modules.pushforward t).obj (SheafOfModules.unit X.ringCatSheaf)) h) =
    SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom := by
  subst h
  rw [eqToHom_refl, Category.comp_id]

/-- The ideal map induced by a commuting square, before scalar extension. -/
def idealPushforwardMap
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    idealModule i ⟶ (Scheme.Modules.pushforward f).obj (idealModule i') := by
  let F := Scheme.Modules.pushforward f
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let α := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  let β := SheafOfModules.unitToPushforwardObjUnit i'.toRingCatSheafHom
  let ηf := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let ηg := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let u := SheafOfModules.unit Q'.ringCatSheaf
  let c : (Scheme.Modules.pushforward (g ≫ i)).obj u ≅
      (Scheme.Modules.pushforward (i' ≫ f)).obj u :=
    eqToIso (congrArg (fun t : Q' ⟶ W => (Scheme.Modules.pushforward t).obj u) h)
  let b := (Scheme.Modules.pushforward i).map ηg ≫
    (Scheme.Modules.pushforwardComp g i).hom.app u ≫ c.hom ≫
      (Scheme.Modules.pushforwardComp i' f).inv.app u
  have hb : α ≫ b = ηf ≫ F.map β := by
    dsimp only [b]
    simp only [← Category.assoc]
    have h1 := s2e_structureModule_map_comp g i
    simp only [← Category.assoc] at h1
    rw [h1]
    simp only [Category.assoc]
    change SheafOfModules.unitToPushforwardObjUnit (g ≫ i).toRingCatSheafHom ≫
      c.hom ≫ (Scheme.Modules.pushforwardComp i' f).inv.app u = _
    rw [← Category.assoc]
    dsimp only [c, eqToIso, u]
    rw [structureMap_congr h]
    rw [← s2e_structureModule_map_comp i' f]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  exact kernel.map α (F.map β) ηf b hb ≫ (PreservesKernel.iso F β).inv

/-- The ideal comparison respects the actual kernel inclusions. -/
lemma idealPushforwardMap_inclusion
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    idealPushforwardMap i i' f g h ≫
      (Scheme.Modules.pushforward f).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i'.toRingCatSheafHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  unfold idealPushforwardMap
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- Scalar extension of the natural ideal map. -/
def idealPullbackMap
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    (Scheme.Modules.pullback f).obj (idealModule i) ⟶ idealModule i' :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (idealPushforwardMap i i' f g h)

/-- The scalar-extended ideal comparison respects the structure-module map. -/
lemma idealPullbackMap_inclusion
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    idealPullbackMap i i' f g h ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit i'.toRingCatSheafHom) =
      (Scheme.Modules.pullback f).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, idealPullbackMap, Equiv.apply_symm_apply,
    idealPushforwardMap_inclusion, Adjunction.homEquiv_naturality_left]
  congr 1
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom).symm

/-- The natural conormal comparison induced by a commuting square. -/
def comparisonMap
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    (Scheme.Modules.pullback g).obj (sheaf i) ⟶ sheaf i' :=
  ((Scheme.Modules.pullbackComp g i).app (idealModule i)).hom ≫
    eqToHom (congrArg (fun t : Q' ⟶ W =>
      (Scheme.Modules.pullback t).obj (idealModule i)) h) ≫
    ((Scheme.Modules.pullbackComp i' f).app (idealModule i)).inv ≫
    (Scheme.Modules.pullback i').map (idealPullbackMap i i' f g h)

end AlgebraicGeometry.Conormal
