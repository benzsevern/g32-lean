import HodgeLean.Foundations.Curves.CurvePoints

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual local homomorphism of a complex point is an augmentation for the prescribed complex stalk scalars.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_complex_point_augmentation
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (x : ComplexPoint X) :
    letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
      (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    X.left.presheaf.stalk x.underlying →ₐ[ℂ] ℂ := by
  letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  refine ⟨x.stalkHom.hom, ?_⟩
  have he : CommRingCat.ofHom (HodgeLean.Foundations.Curves.stalkC x.underlying) ≫
      x.stalkHom = 𝟙 (CommRingCat.of ℂ) := by
    apply Spec.map_injective
    rw [Spec.map_comp,
      ← HodgeLean.Foundations.Curves.fromSpecStalk_comp_hom' x.underlying,
      ← Category.assoc]
    change (Spec.map (Scheme.stalkClosedPointTo x.left) ≫
      X.left.fromSpecStalk (x.left (IsLocalRing.closedPoint ℂ))) ≫ X.hom = _
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Over.w x, Spec.map_id]
    rfl
  intro c
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => f.hom c) he

#print axioms s2e_complex_point_augmentation
end HodgeLean.Foundations.Program
