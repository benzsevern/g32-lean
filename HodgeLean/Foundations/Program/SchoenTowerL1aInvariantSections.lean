import HodgeLean.Foundations.Program.SchoenTowerL1aComplexCover
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Sections on finite quotient restrictions

Implication from complex point surjectivity and reducedness to injectivity of
sections on restricted finite maps. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The restricted finite map has injective pullback on global sections when its target is reduced.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5, dominant maps to reduced schemes. -/
theorem s2v_l1a_restricted_sections_injective
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom] [IsReduced Y.left]
    (f : X ⟶ Y) [IsFinite f.left]
    (hsurj : Function.Surjective (Point.map f)) (U : Y.left.Opens) :
    Function.Injective (f.left ∣_ U).appTop.hom := by
  let : AlgebraicGeometry.Surjective f.left :=
    s2v_l1a_scheme_surjective_of_complex_surjective X Y f hsurj
  let : AlgebraicGeometry.Surjective (f.left ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @AlgebraicGeometry.Surjective)
      (inferInstance : AlgebraicGeometry.Surjective f.left) U
  let : IsSchemeTheoreticallyDominant (f.left ∣_ U) :=
    IsSchemeTheoreticallyDominant.of_isDominant (f.left ∣_ U)
  exact (f.left ∣_ U).app_injective ⊤

/-- Sections pulled back through an invariant map are invariant under the specified endomorphisms.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of sections. -/
theorem s2v_l1a_sections_image_invariant
    {X Y : Scheme} {T : Type*} (q : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ q = q) (s : Γ(Y, ⊤)) (t : T) :
    (a t).appTop.hom (q.appTop.hom s) = q.appTop.hom s := by
  have h := congrArg (fun f : X ⟶ Y => f.appTop) (ha t)
  rw [Scheme.Hom.comp_appTop] at h
  exact congrArg (fun f => f.hom s) h

end HodgeLean.Foundations.Program
