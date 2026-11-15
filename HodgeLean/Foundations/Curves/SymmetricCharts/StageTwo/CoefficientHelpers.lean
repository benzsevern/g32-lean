import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CoordinateHelpers
import HodgeLean.Foundations.Program.SchoenCycleSectionPolynomialEvaluation
import HodgeLean.Foundations.Program.SchoenTowerOverSections

/-! # Elementary coefficient evaluation on actual quotient charts

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
attribute [local instance] overSpecAlgebra

/-- Pullback equations for elementary coefficient sections retain their exact scalar values.
Source: Hartshorne, Algebraic Geometry, II.2; fundamental theorem of symmetric polynomials.
HC no distance; AV milestone no distance.
-/
theorem elementary_section_values (X Y : Over (Spec ↧ℂ)) (q : X ⟶ Y) (n : ℕ)
    (r : Fin n → Γ(X.left, ⊤)) (c : Fin n → Γ(Y.left, ⊤))
    (hc : ∀ j, q.left.appTop.hom (c j) = MvPolynomial.aeval (R := ℂ) r
      (MvPolynomial.esymm (Fin n) ℂ (j.val+1))) (p : ComplexPoint X) (j : Fin n) :
    Point.evaluate ⊤ (c j) (Point.map q p) =
      MvPolynomial.eval (fun i => Point.evaluate ⊤ (r i) p)
        (MvPolynomial.esymm (Fin n) ℂ (j.val+1)) := by
  have H : Point.evaluate ⊤ (c j) (Point.map q p) =
      Point.evaluate ⊤ (q.left.appTop.hom (c j)) p := by
    simpa only [TopologicalSpace.Opens.map_top, Scheme.Hom.appTop] using
      Point.evaluate_map q ⊤ (c j) p
  rw [H, hc]
  have he := s2e_section_polynomial_evaluate X ⊤ (Fin n)
    (MvPolynomial.aeval (R := ℂ) r) p (by trivial)
    (MvPolynomial.esymm (Fin n) ℂ (j.val+1))
  simpa only [MvPolynomial.aeval_X, MvPolynomial.aeval_eq_eval] using he

/-- A section-defined map to polynomial affine space retains every variable value.
Source: Hartshorne, Algebraic Geometry, II.2.
HC no distance; AV milestone no distance.
-/
theorem section_map_coordinate_value (Y : Over (Spec ↧ℂ)) (n : ℕ)
    (G : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.left, ⊤)) (p : ComplexPoint Y)
    (j : Fin n) :
    coordinateValue n (Point.map (s2e_section_defined_affine_map Y _ G) p) j =
      Point.evaluate ⊤ (G (MvPolynomial.X j)) p := by
  let f := s2e_section_defined_affine_map Y _ G
  have hΓ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom G.toRingHom)
  have he : f.left.appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin n) ℂ)).inv
      (MvPolynomial.X j)) = G (MvPolynomial.X j) :=
    congrArg (fun k : CommRingCat.of (MvPolynomial (Fin n) ℂ) ⟶ Γ(Y.left, ⊤) =>
      k.hom (MvPolynomial.X j)) hΓ
  rw [coordinateValue, ComplexPoint.evaluate_top_eq_appTop]
  change (Scheme.ΓSpecIso ↧ℂ).hom ((p.left ≫ f.left).appTop _) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, he]

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
