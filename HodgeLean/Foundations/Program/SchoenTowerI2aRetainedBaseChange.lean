import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedReesLift
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every actual base change retains the factorization universal property
for the pulled-back Cartier test, with the specified pullback projection.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `pullback.lift` and `Scheme.IdealSheafData.comap_comp`. -/
theorem s2v_i2a_retained_cartier_universal_base_change
    (Q : Scheme.{0}) (Y B A : Over Q) (b : B ⟶ Y) (c : A ⟶ Y)
    (K : Y.left.IdealSheafData)
    (huniv : ∀ (T : Over Q) (f : T ⟶ Y),
      (∀ p : T.left, ∃ U : T.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! v : T ⟶ B, v ≫ b = f)
    (T : Over Q) (f : T ⟶ A)
    (hfree : ∀ p : T.left, ∃ U : T.left.affineOpens, p ∈ U.1 ∧
      Nonempty ((((K.comap c.left).comap f.left).ideal U)
        ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) :
    ∃! v : T ⟶ pullback b c, v ≫ pullback.snd b c = f := by
  have hfree' : ∀ p : T.left, ∃ U : T.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap (f ≫ c).left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U)) := by
    change ∀ p : T.left, ∃ U : T.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap (f.left ≫ c.left)).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))
    rw [Scheme.IdealSheafData.comap_comp]
    exact hfree
  obtain ⟨v, hv, huniq⟩ := huniv T (f ≫ c) hfree'
  refine ⟨pullback.lift v f hv, pullback.lift_snd _ _ _, ?_⟩
  intro w hw
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    apply huniq
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  · simpa only [pullback.lift_snd] using hw

end HodgeLean.Foundations.Program
