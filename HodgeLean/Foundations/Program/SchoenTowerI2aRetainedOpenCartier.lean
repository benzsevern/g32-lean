import HodgeLean.Foundations.Program.SchoenTowerI2aCartierOpenRestriction
import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedBaseChange

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual open base change of an integral retained Cartier morphism
satisfies the same pointwise ideal-module test for its specified projection.
Source: Hartshorne, Algebraic Geometry, II.6, locality of effective Cartier divisors;
Mathlib, `IsPullback.map` and `Scheme.IdealSheafData.comap_comp`. -/
theorem s2v_i2a_retained_open_base_change_cartier
    (Q : Scheme.{0}) (Y B A : Over Q) [IsIntegral B.left]
    (b : B ⟶ Y) (c : A ⟶ Y) [IsOpenImmersion c.left]
    (K : Y.left.IdealSheafData)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U))) :
    ∀ q : (pullback b c).left, ∃ U : (pullback b c).left.affineOpens, q ∈ U.1 ∧
      Nonempty ((((K.comap c.left).comap (pullback.snd b c).left).ideal U)
        ≃ₗ[Γ((pullback b c).left, U)] Γ((pullback b c).left, U)) := by
  haveI : IsOpenImmersion (pullback.fst b c).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (((IsPullback.of_hasPullback b c).map (Over.forget Q)).flip) (show IsOpenImmersion c.left from inferInstance)
  intro q
  letI : Nonempty (pullback b c).left := ⟨q⟩
  haveI : IsIntegral (pullback b c).left :=
    isIntegral_of_isOpenImmersion (pullback.fst b c).left
  have H := s2v_i2a_cartier_test_open_restriction (pullback.fst b c).left
    (K.comap b.left) hcartier q
  have hsq : (pullback.fst b c).left ≫ b.left = (pullback.snd b c).left ≫ c.left :=
    congrArg (fun f => f.left) (pullback.condition (f := b) (g := c))
  rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp] at H
  exact H

end HodgeLean.Foundations.Program
