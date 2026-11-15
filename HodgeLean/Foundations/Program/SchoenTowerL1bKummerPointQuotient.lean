import HodgeLean.Foundations.Program.SchoenProjectiveActionQuotient
import HodgeLean.Foundations.Mathlib.ZmtIso
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A proper map of integral complex schemes with smooth target and bijective
rational point map is an isomorphism. -/
theorem s2v_l1b_isIso_of_point_bijective
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [Smooth Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hbij : Function.Bijective (Point.map f)) : IsIso f.left := by
  have hclosed (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
      IsClosed ({f.left x} : Set Y.left) := by
    simpa only [Set.image_singleton] using f.left.isClosedMap _ hx
  have hpoint (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
      ∃ p : ComplexPoint X, p.left (IsLocalRing.closedPoint ℂ) = x :=
    ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (by simp),
      pointOfClosedPoint_apply X.hom x hx _⟩
  have hinj : ∀ ⦃x y : X.left⦄, IsClosed {x} → IsClosed {y} →
      f.left x = f.left y → x = y := by
    intro x y hx hy hxy
    obtain ⟨p, hp⟩ := hpoint x hx
    obtain ⟨q, hq⟩ := hpoint y hy
    have he : Point.map f p = Point.map f q := by
      apply Over.OverMorphism.ext
      apply ext_of_apply_closedPoint_eq Y.hom (Over.w _) (Over.w _)
      change f.left (p.left (IsLocalRing.closedPoint ℂ)) =
        f.left (q.left (IsLocalRing.closedPoint ℂ))
      rw [hp, hq, hxy]
    have := congrArg (fun p : ComplexPoint X => p.left (IsLocalRing.closedPoint ℂ))
      (hbij.injective he)
    simpa only [hp, hq] using this
  have hsurj : ∀ y : Y.left, IsClosed {y} →
      ∃ x : X.left, IsClosed {x} ∧ f.left x = y := by
    intro y hy
    let p : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy) (by simp)
    obtain ⟨q, hq⟩ := hbij.surjective p
    refine ⟨q.left (IsLocalRing.closedPoint ℂ), ?_, ?_⟩
    · haveI : IsClosedImmersion (q.left ≫ X.hom) := by
        rw [Over.w q]
        change IsClosedImmersion (𝟙 (Spec ↧ℂ))
        infer_instance
      haveI : IsClosedImmersion q.left := IsClosedImmersion.of_comp q.left X.hom
      simpa only [Set.image_singleton] using
        (show IsClosedMap q.left from q.left.isClosedMap) _
          (IsLocalRing.isClosed_singleton_closedPoint ℂ)
    · have he := congrArg (fun p : ComplexPoint Y => p.left (IsLocalRing.closedPoint ℂ)) hq
      exact he.trans (pointOfClosedPoint_apply Y.hom y hy _)
  have hres (x : X.left) (hx : IsClosed {x}) : IsIso (f.left.residueFieldMap x) := by
    have he : (residueFieldIsoBase Y.hom (f.left x) (hclosed x hx)).inv ≫
        f.left.residueFieldMap x = (residueFieldIsoBase X.hom x hx).inv := by
      apply Spec.map_injective
      rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, SpecMap_residueFieldIsoBase_inv,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Over.w]
    have he' : f.left.residueFieldMap x =
        (residueFieldIsoBase Y.hom (f.left x) (hclosed x hx)).hom ≫
          (residueFieldIsoBase X.hom x hx).inv := by
      rw [← he, Iso.hom_inv_id_assoc]
    rw [he']
    infer_instance
  exact zmtiso_isIso_of_proper_injective_normal X.hom Y.hom f.left
    (zmtiso_normal_of_smooth Y.left Y.hom) (Over.w f) hinj hsurj hres

end HodgeLean.Foundations.Program
