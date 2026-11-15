import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Commute.Units

/-! # The retained periodic deck map is an isomorphism
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- A positive-period endomorphism transports to an isomorphism through the retained stage-zero identification.
Source: Mathlib, IsUnit.of_pow_eq_one and CategoryTheory.isUnit_iff_isIso. -/
theorem s2v_i2a_periodic_retained_deck_isIso
    {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) (f : X ⟶ X) (g : Y ⟶ Y)
    (hfg : f ≫ e.hom = e.hom ≫ g) (m : ℕ) (hm : 0 < m)
    (hperiod : (End.of f) ^ m = 1) : IsIso g := by
  haveI : IsIso f := (CategoryTheory.isUnit_iff_isIso (End.of f)).mp
    (IsUnit.of_pow_eq_one hperiod hm.ne')
  haveI : IsIso (e.hom ≫ g) := by rw [← hfg]; infer_instance
  exact IsIso.of_isIso_comp_left e.hom g

/-- Intertwining endomorphisms intertwines all their nonnegative powers.
Source: Mathlib, CategoryTheory.End.mul_asHom and pow_succ'. -/
theorem s2v_i2a_intertwined_endomorphism_powers
    {C : Type*} [Category C] {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) (u : X ⟶ Y)
    (h : f ≫ u = u ≫ g) (k : ℕ) :
    ((End.of f) ^ k).asHom ≫ u = u ≫ ((End.of g) ^ k).asHom := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ', End.mul_asHom]
    rw [Category.assoc, h, ← Category.assoc, ih, Category.assoc]

/-- The retained stage-zero identification transports the specified deck period to the original scheme.
Source: Mathlib, cancellation of an isomorphism and powers of intertwined endomorphisms. -/
theorem s2v_i2a_retained_deck_period
    {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) (f : X ⟶ X) (g : Y ⟶ Y)
    (hfg : f ≫ e.hom = e.hom ≫ g) (m : ℕ) (hperiod : (End.of f) ^ m = 1) :
    (End.of g) ^ m = 1 := by
  have H := s2v_i2a_intertwined_endomorphism_powers f g e.hom hfg m
  apply End.ext
  apply (cancel_epi e.hom).mp
  simpa only [hperiod, End.one_asHom, Category.id_comp, Category.comp_id] using H.symm

end HodgeLean.Foundations.Program
