import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedReesLift

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained universal property compares actual scheme maps from any
Cartier source directly, using their common map to the specified base.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_cartier_scheme_lift_unique
    (Q : Scheme.{0}) (Y B : Over Q) (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (huniv : ∀ (T : Over Q) (f : T ⟶ Y),
      (∀ p : T.left, ∃ U : T.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! v : T ⟶ B, v ≫ b = f)
    (X : Scheme.{0}) (α β : X ⟶ B.left)
    (hbase : α ≫ b.left = β ≫ b.left)
    (hfree : ∀ p : X, ∃ U : X.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap (β ≫ b.left)).ideal U) ≃ₗ[Γ(X, U)] Γ(X, U))) :
    α = β := by
  let T : Over Q := Over.mk (β ≫ B.hom)
  have hα : α ≫ B.hom = β ≫ B.hom := by
    have H := congrArg (fun f : X ⟶ Y.left => f ≫ Y.hom) hbase
    simpa only [Category.assoc, b.w] using H
  let a : T ⟶ B := Over.homMk α hα
  let c : T ⟶ B := Over.homMk β rfl
  obtain ⟨v, hv, hu⟩ := huniv T (c ≫ b) hfree
  have hab : a ≫ b = c ≫ b := Over.OverMorphism.ext hbase
  have hac : a = c := (hu a hab).trans (hu c rfl).symm
  exact congrArg (fun f : T ⟶ B => f.left) hac

end HodgeLean.Foundations.Program
