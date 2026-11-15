import HodgeLean.Foundations.QuotientDuality.LocalHolomorphicCharts
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! Regular coordinate evaluation across an arbitrary open immersion. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

theorem evaluate_openImmersion {X Y : Over (Spec ↧ℂ)}
    (j : X ⟶ Y) [IsOpenImmersion j.left] (V : X.left.Opens)
    (t : Γ(X.left, V)) (z : ComplexPoint X) :
    Point.evaluate (j.left ''ᵁ V) ((j.left.appIso V).inv t) (Point.map j z) =
      Point.evaluate V t z := by
  rw [Point.evaluate_map]
  let e : j.left ⁻¹ᵁ j.left ''ᵁ V = V := j.left.preimage_image_eq V
  let q := j.left.app (j.left ''ᵁ V) ((j.left.appIso V).inv t)
  have hq : q = X.left.presheaf.map (eqToHom e).op t := by
    change ((j.left.appIso V).inv ≫ j.left.app (j.left ''ᵁ V)) t = _
    rw [j.left.appIso_inv_app]
  calc
    Point.evaluate (j.left ⁻¹ᵁ j.left ''ᵁ V) q z =
        Point.evaluate V (X.left.presheaf.map (eqToHom e.symm).op q) z :=
      evaluate_eq (Y := X) e q z
    _ = Point.evaluate V t z := by
      congr 2
      rw [hq]
      change (X.left.presheaf.map (eqToHom e).op ≫
        X.left.presheaf.map (eqToHom e.symm).op) t = t
      rw [← Functor.map_comp]
      simp

#print axioms evaluate_openImmersion
end HodgeLean.Foundations.QuotientDuality
