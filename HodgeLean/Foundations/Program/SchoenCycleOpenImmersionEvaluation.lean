import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartPoints

/-! # Evaluation across actual open immersions -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Evaluation commutes with the actual section isomorphism of any open immersion over the complex field.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_evaluate_openImmersion_appIso {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [IsOpenImmersion f.left] (U : X.left.Opens) (t : Γ(X.left, U)) (z : ComplexPoint X) :
    Point.evaluate (f.left ''ᵁ U) ((f.left.appIso U).inv t) (Point.map f z) =
      Point.evaluate U t z := by
  rw [Point.evaluate_map]
  let e : f.left ⁻¹ᵁ f.left ''ᵁ U = U := f.left.preimage_image_eq U
  let q := f.left.app (f.left ''ᵁ U) ((f.left.appIso U).inv t)
  have hq : q = X.left.presheaf.map (eqToHom e).op t := by
    change ((f.left.appIso U).inv ≫ f.left.app (f.left ''ᵁ U)) t = _
    rw [f.left.appIso_inv_app]
  calc
    Point.evaluate (f.left ⁻¹ᵁ f.left ''ᵁ U) q z =
        Point.evaluate U (X.left.presheaf.map (eqToHom e.symm).op q) z :=
      evaluate_eq e q z
    _ = Point.evaluate U t z := by
      congr 2
      rw [hq]
      change (X.left.presheaf.map (eqToHom e).op ≫
        X.left.presheaf.map (eqToHom e.symm).op) t = t
      rw [← Functor.map_comp]
      simp

end HodgeLean.Foundations.Program
