import HodgeLean.Foundations.Program.SchoenTowerI2aDeckCoefficients
import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedDeck

/-! # Powers of the actual original-field deck map
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The generic-point deck square intertwines every power of the field and scheme maps.
Source: Mathlib, Spec.map_comp, powers of ring equivalences and CategoryTheory.End.mul_asHom. -/
theorem s2v_i2a_field_deck_power_square
    {K : Type*} [CommRing K] {W : Scheme} (η : Spec (CommRingCat.of K) ⟶ W)
    (f : W ⟶ W) (δ : K ≃+* K)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η ≫ f) (k : ℕ) :
    Spec.map (CommRingCat.ofHom (δ ^ k).toRingHom) ≫ η =
      η ≫ ((End.of f) ^ k).asHom := by
  induction k with
  | zero =>
    change Spec.map (𝟙 (CommRingCat.of K)) ≫ η = η ≫ 𝟙 W
    simp
  | succ k ih =>
    have hcomp : CommRingCat.ofHom (δ * δ ^ k).toRingHom =
        CommRingCat.ofHom (δ ^ k).toRingHom ≫ CommRingCat.ofHom δ.toRingHom := rfl
    rw [pow_succ' δ k, hcomp, Spec.map_comp, Category.assoc, ih,
      ← Category.assoc, hδ, Category.assoc, pow_succ, End.mul_asHom]

/-- A scheme deck period is a period of its field automorphism when the generic-point morphism is a monomorphism.
Source: Mathlib, faithfulness of Spec and cancellation of the generic-point morphism. -/
theorem s2v_i2a_field_deck_period
    {K : Type*} [CommRing K] {W : Scheme} (η : Spec (CommRingCat.of K) ⟶ W) [Mono η]
    (f : W ⟶ W) (δ : K ≃+* K)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ η = η ≫ f)
    (m : ℕ) (hperiod : (End.of f) ^ m = 1) : δ ^ m = 1 := by
  have H := s2v_i2a_field_deck_power_square η f δ hδ m
  rw [hperiod, End.one_asHom, Category.comp_id] at H
  have hSpec : Spec.map (CommRingCat.ofHom (δ ^ m).toRingHom) = 𝟙 _ := by
    apply (cancel_mono η).mp
    simpa only [Category.id_comp] using H
  have hRing : CommRingCat.ofHom (δ ^ m).toRingHom = 𝟙 (CommRingCat.of K) := by
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    change Spec.map (CommRingCat.ofHom (δ ^ m).toRingHom) = Spec.map (𝟙 (CommRingCat.of K))
    rw [Spec.map_id]
    exact hSpec
  exact RingEquiv.toRingHom_injective (congrArg CommRingCat.Hom.hom hRing)

end HodgeLean.Foundations.Program
