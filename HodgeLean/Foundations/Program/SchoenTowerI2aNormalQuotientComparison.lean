import HodgeLean.Foundations.Mathlib.ZmtIso
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Comparison with a normal retained quotient
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A proper morphism of integral complex schemes bijective on complex points is an isomorphism onto a normal target.
Source: Stacks Project, tag 0AB1; Mathlib, residueFieldIsoBase and the checked Zariski main isomorphism criterion. -/
theorem s2v_i2a_proper_point_bijective_isIso
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (hY : zmtiso_IsNormal Y.left)
    (hbij : Function.Bijective (Point.map f)) : IsIso f.left := by
  apply zmtiso_isIso_of_proper_injective_normal X.hom Y.hom f.left hY (Over.w f)
  · intro x₁ x₂ hx₁ hx₂ heq
    let p₁ : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x₁ hx₁)
      (pointOfClosedPoint_comp X.hom x₁ hx₁)
    let p₂ : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x₂ hx₂)
      (pointOfClosedPoint_comp X.hom x₂ hx₂)
    have hp₁ : p₁.left (IsLocalRing.closedPoint ℂ) = x₁ :=
      pointOfClosedPoint_apply X.hom x₁ hx₁ _
    have hp₂ : p₂.left (IsLocalRing.closedPoint ℂ) = x₂ :=
      pointOfClosedPoint_apply X.hom x₂ hx₂ _
    have hp : Point.map f p₁ = Point.map f p₂ := by
      apply Over.OverMorphism.ext
      apply ext_of_apply_closedPoint_eq Y.hom (Over.w (p₁ ≫ f)) (Over.w (p₂ ≫ f))
      change f.left (p₁.left (IsLocalRing.closedPoint ℂ)) =
        f.left (p₂.left (IsLocalRing.closedPoint ℂ))
      rw [hp₁, hp₂, heq]
    have H := congrArg (fun p : ComplexPoint X => p.left (IsLocalRing.closedPoint ℂ))
      (hbij.injective hp)
    rwa [hp₁, hp₂] at H
  · intro y hy
    let p : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy)
      (pointOfClosedPoint_comp Y.hom y hy)
    obtain ⟨q, hq⟩ := hbij.surjective p
    have hqc : IsClosed ({q.left (IsLocalRing.closedPoint ℂ)} : Set X.left) :=
      ((pointEquivClosedPoint X.hom) ⟨q.left, Over.w q⟩).property
    refine ⟨q.left (IsLocalRing.closedPoint ℂ), hqc, ?_⟩
    have H := congrArg (fun p : ComplexPoint Y => p.left (IsLocalRing.closedPoint ℂ)) hq
    have hp : p.left (IsLocalRing.closedPoint ℂ) = y :=
      pointOfClosedPoint_apply Y.hom y hy _
    exact H.trans hp
  · intro x hx
    have hfx : IsClosed ({f.left x} : Set Y.left) := by
      simpa only [Set.image_singleton] using f.left.isClosedMap {x} hx
    have H : (residueFieldIsoBase Y.hom (f.left x) hfx).inv ≫ f.left.residueFieldMap x =
        (residueFieldIsoBase X.hom x hx).inv := by
      apply Spec.map_injective
      rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, SpecMap_residueFieldIsoBase_inv,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Over.w f]
    have heq : f.left.residueFieldMap x =
        (residueFieldIsoBase Y.hom (f.left x) hfx).hom ≫
          (residueFieldIsoBase X.hom x hx).inv := by
      rw [← H, Iso.hom_inv_id_assoc]
    rw [heq]
    infer_instance

end HodgeLean.Foundations.Program
