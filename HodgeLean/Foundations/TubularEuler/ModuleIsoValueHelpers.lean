import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Evaluation of mapped module isomorphisms

The evaluation law is checked before specializing the source category or modules.
HC no distance; AV milestone no distance. -/

universe u v
open CategoryTheory
namespace HodgeLean.Foundations.TubularEuler

theorem moduleIso_map_trans_apply
    {R : Type u} [Ring R] {C : Type v} [Category C]
    (F : C ⥤ ModuleCat R) {X Y : C} {T : ModuleCat R}
    (i : X ≅ Y) (e : F.obj Y ≅ T) (x : F.obj X) :
    (F.mapIso i ≪≫ e).hom x = e.hom (F.map i.hom x) := rfl

theorem moduleIso_apply_eq_of_factorization
    {R : Type u} [Ring R] {C : Type v} [Category C]
    (F : C ⥤ ModuleCat R) {X Y : C} {T : ModuleCat R}
    (i : X ≅ Y) (e : F.obj Y ≅ T) (a : F.obj X ≅ T)
    (ha : a = F.mapIso i ≪≫ e) (x : F.obj X) (y : T)
    (h : e.hom (F.map i.hom x) = y) : a.hom x = y := by
  subst a
  exact (moduleIso_map_trans_apply F i e x).trans h

theorem moduleIso_apply_eq_of_eq
    {R : Type u} [Ring R] {P T : ModuleCat R}
    (a b : P ≅ T) (hab : a = b) (x : P) (y : T)
    (h : b.hom x = y) : a.hom x = y := by
  subst a
  exact h

#print axioms moduleIso_apply_eq_of_eq

#print axioms moduleIso_apply_eq_of_factorization

#print axioms moduleIso_map_trans_apply

end HodgeLean.Foundations.TubularEuler
