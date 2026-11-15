import HodgeLean.Foundations.TubularEuler.ModuleIsoValueHelpers

/-! # Evaluation through a mapped middle isomorphism

The three-stage evaluation is checked on abstract modules before scalar extension.
HC no distance; AV milestone no distance. -/

universe u v w
open CategoryTheory
namespace HodgeLean.Foundations.TubularEuler

theorem moduleIso_apply_eq_of_middle_map
    {R : Type u} [Ring R] {C : Type v} [Category C]
    (F : C ⥤ ModuleCat R) {X Y : C} {P T : ModuleCat R}
    (a : P ≅ F.obj X) (i : X ≅ Y) (b : F.obj Y ≅ T) (e : P ≅ T)
    (he : e = a ≪≫ F.mapIso i ≪≫ b) (x : P) (v : F.obj X) (y : T)
    (ha : a.hom x = v) (h : b.hom (F.map i.hom v) = y) : e.hom x = y := by
  subst e
  simpa only [Iso.trans_hom, ModuleCat.comp_apply, Functor.mapIso_hom, ha] using h

theorem moduleIso_apply_eq_of_trans_values
    {R : Type u} [Ring R] {P Q T : ModuleCat R}
    (a : P ≅ Q) (b : Q ≅ T) (e : P ≅ T) (he : e = a ≪≫ b)
    (x : P) (v : Q) (y : T) (ha : a.hom x = v) (hb : b.hom v = y) :
    e.hom x = y := by
  subst e
  simpa only [Iso.trans_hom, ModuleCat.comp_apply, ha] using hb

theorem moduleIso_apply_eq_of_two_maps
    {R : Type u} [Ring R] {C : Type v} [Category C]
    (F : C ⥤ ModuleCat R) {X Y Z : C} {P : ModuleCat R}
    (a : P ≅ F.obj X) (i : X ≅ Y) (j : Y ≅ Z) (e : P ≅ F.obj Z)
    (he : e = a ≪≫ F.mapIso i ≪≫ F.mapIso j) (x : P) (y : F.obj Z)
    (h : F.map j.hom (F.map i.hom (a.hom x)) = y) : e.hom x = y := by
  subst e
  simpa only [Iso.trans_hom, ModuleCat.comp_apply, Functor.mapIso_hom] using h

theorem moduleIso_apply_eq_of_functor_natIso
    {R : Type u} [Ring R] {C : Type v} [Category C] {D : Type w} [Category D]
    (F : C ⥤ ModuleCat R) (G H : D ⥤ C) (α : G ≅ H)
    {X Y : D} {P : ModuleCat R}
    (a : P ≅ F.obj (G.obj X)) (i : X ≅ Y) (e : P ≅ F.obj (H.obj Y))
    (he : e = a ≪≫ F.mapIso (G.mapIso i) ≪≫ F.mapIso (α.app Y))
    (x : P) (y : F.obj (H.obj Y))
    (h : F.map (α.hom.app Y) (F.map (G.map i.hom) (a.hom x)) = y) :
    e.hom x = y := by
  subst e
  simpa only [Iso.trans_hom, ModuleCat.comp_apply, Functor.mapIso_hom, Iso.app_hom] using h

#print axioms moduleIso_apply_eq_of_functor_natIso

#print axioms moduleIso_apply_eq_of_two_maps

#print axioms moduleIso_apply_eq_of_trans_values

#print axioms moduleIso_apply_eq_of_middle_map

end HodgeLean.Foundations.TubularEuler
