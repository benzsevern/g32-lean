import HodgeLean.Foundations.Program.SchoenTowerI2aFieldDeckPowers
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Detecting retained deck periods in the original field
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A period of the field deck action is a period of its actual separated scheme action.
Source: Mathlib, ext_of_isDominant_of_isSeparated and the generic-point deck square. -/
theorem s2v_i2a_scheme_deck_period_of_field
    {K : Type*} [CommRing K] {S : Scheme} (W : Over S)
    [IsReduced W.left] [IsSeparated W.hom]
    (η : Spec (CommRingCat.of K) ⟶ W.left) [IsDominant η]
    (f : W ⟶ W) (δ : K ≃+* K)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η ≫ f.left)
    (k : ℕ) (hk : δ ^ k = 1) : (End.of f) ^ k = 1 := by
  have H := s2v_i2a_field_deck_power_square η f.left δ hδ k
  rw [hk] at H
  change Spec.map (𝟙 (CommRingCat.of K)) ≫ η =
    η ≫ ((End.of f.left) ^ k).asHom at H
  have Hη : η ≫ ((End.of f.left) ^ k).asHom = η := by
    simpa only [Spec.map_id, Category.id_comp] using H.symm
  apply End.ext
  apply Over.OverMorphism.ext
  change (((End.of f) ^ k).asHom).left = 𝟙 W.left
  have hleft : (((End.of f) ^ k).asHom).left = ((End.of f.left) ^ k).asHom := by
    have H := map_pow ((Over.forget S).mapEnd W) (End.of f) k
    change End.of ((((End.of f) ^ k).asHom).left) = (End.of f.left) ^ k at H
    exact congrArg End.asHom H
  rw [hleft]
  apply ext_of_isDominant_of_isSeparated W.hom (ι := η)
  · simpa only [hleft, Over.id_left, Category.id_comp] using
      (Over.w (((End.of f) ^ k).asHom))
  · simpa only [Over.id_left, Category.comp_id] using Hη

/-- The field and actual separated scheme deck actions have exactly the same order.
Source: Mathlib, orderOf_eq_orderOf_iff and determination of separated scheme maps on a dominant field point. -/
theorem s2v_i2a_field_deck_order_eq
    {K : Type*} [CommRing K] {S : Scheme} (W : Over S)
    [IsReduced W.left] [IsSeparated W.hom]
    (η : Spec (CommRingCat.of K) ⟶ W.left) [IsDominant η] [Mono η]
    (f : W ⟶ W) (δ : K ≃+* K)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η ≫ f.left) :
    orderOf δ = orderOf (End.of f) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  constructor
  · exact s2v_i2a_scheme_deck_period_of_field W η f δ hδ k
  · intro h
    have H := congrArg ((Over.forget S).mapEnd W) h
    rw [map_pow, map_one] at H
    change (End.of f.left) ^ k = 1 at H
    exact s2v_i2a_field_deck_period η f.left δ hδ k H

end HodgeLean.Foundations.Program
