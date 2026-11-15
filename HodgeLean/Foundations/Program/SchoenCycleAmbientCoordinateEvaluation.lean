import HodgeLean.Foundations.Program.SchoenCycleOpenTopSectionEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Ambient analytic coordinate evaluations retain the original supplied section values on the coordinate neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_ambient_coordinate_section_evaluate
    (X : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (p : ComplexPoint X) (D : LocalEtaleCoordinates X n p.underlying)
    (q : ComplexPoint X) (hq : q ∈ Point.overOpen D.neighborhood) (i : Fin n) :
    Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) q =
      Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i)) q := by
  let z := (ComplexPoint.openHomeomorph X D.neighborhood).symm ⟨q, hq⟩
  have hz : Point.map (ComplexPoint.openInclusion X D.neighborhood) z = q :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph X D.neighborhood).apply_symm_apply ⟨q, hq⟩)
  calc
    Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) q =
        D.ambientAnalyticCoordinates ⟨q, hq⟩ i :=
      (D.ambientAnalyticCoordinates_apply_eq_evaluate ⟨q, hq⟩ i).symm
    _ = Point.evaluate ⊤ (D.coordinateRingHomOnOpen (MvPolynomial.X i)) z :=
      D.analyticCoordinates_apply_eq_evaluate z i
    _ = Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X i))
        (Point.map (ComplexPoint.openInclusion X D.neighborhood) z) :=
      s2e_complex_open_top_section_evaluate X D.neighborhood _ z
    _ = _ := by rw [hz]

#print axioms s2e_ambient_coordinate_section_evaluate
end HodgeLean.Foundations.Program
