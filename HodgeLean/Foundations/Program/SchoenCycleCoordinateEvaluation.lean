import HodgeLean.Foundations.Program.SchoenCycleCoordinateStalkPullback
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

/-! # Actual scalar evaluation of coordinate-defined scheme morphisms -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A scheme morphism specified by global coordinate sections evaluates those
same sections at every actual complex point.
Source: Hartshorne, Algebraic Geometry, II.2; HodgeConjecture,
AlgebraicGeometry.ComplexPoint.affineSpecEquiv_apply. -/
theorem s2e_spec_coordinate_evaluation
    (Y : Over (Spec ↧ℂ)) (P : Type) [CommRing P] [Algebra ℂ P]
    (f : Y ⟶ Over.mk (ComplexPoint.affineSpecStructureMap P))
    (e : CommRingCat.of P ⟶ Γ(Y.left, ⊤))
    (hf : f.left = Y.left.toSpecΓ ≫ Spec.map e) (p : ComplexPoint Y) (r : P) :
    ComplexPoint.affineSpecEquiv P (Point.map f p) r = Point.evaluate ⊤ (e r) p := by
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ f.left.appTop = e := by
    rw [hf]
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv e
  have he : f.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv r) = e r :=
    congrArg (fun k : CommRingCat.of P ⟶ Γ(Y.left, ⊤) => k.hom r) hΓ
  rw [ComplexPoint.affineSpecEquiv_apply, ComplexPoint.evaluate_top_eq_appTop,
    ComplexPoint.evaluate_top_eq_appTop]
  change (Scheme.ΓSpecIso ↧ℂ).hom
      ((p.left ≫ f.left).appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv r)) =
    (Scheme.ΓSpecIso ↧ℂ).hom (p.left.appTop (e r))
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, he]

end HodgeLean.Foundations.Program
