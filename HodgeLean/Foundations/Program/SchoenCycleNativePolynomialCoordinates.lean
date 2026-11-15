import HodgeLean.Foundations.Program.SchoenCycleNativeEtaleCharts
import HodgeLean.Foundations.Program.SchoenCycleCoordinateEvaluation

/-! # Native chart coordinates as polynomial-spectrum morphisms -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The native chart's actual scheme map with target the polynomial spectrum
and its specified complex structure morphism.
Source: Hartshorne, Algebraic Geometry, II.8; HodgeConjecture,
AlgebraicGeometry.LocalEtaleCoordinates.toAffineSpaceOver. -/
def s2e_native_polynomial_coordinates
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x) :
    ComplexPoint.openScheme X D.neighborhood ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap (MvPolynomial (Fin d) ℂ)) :=
  D.toAffineSpaceOver ≫
    (Over.isoMk (AffineSpace.SpecIso (Fin d) ↧ℂ) (by
      change (AffineSpace.SpecIso (Fin d) ↧ℂ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin d) ℂ))) =
          (ComplexPoint.complexAffineSpace (Fin d) ↘ Spec ↧ℂ)
      have h := congrArg (fun q => (AffineSpace.SpecIso (Fin d) ↧ℂ).hom ≫ q)
        (AffineSpace.SpecIso_inv_over (n := Fin d) ↧ℂ)
      simpa only [ComplexPoint.affineSpecStructureMap, MvPolynomial.algebraMap_eq,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h.symm)).hom

/-- The polynomial-spectrum coordinate morphism is the specified affine
section coordinate map.
Source: HodgeConjecture, AlgebraicGeometry.LocalEtaleCoordinates.toAffineSpace. -/
theorem s2e_native_polynomial_coordinates_left
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x) :
    (s2e_native_polynomial_coordinates X d x D).left =
      D.neighborhood.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen) := by
  change D.toAffineSpace ≫ (AffineSpace.SpecIso (Fin d) ↧ℂ).hom = _
  simp only [LocalEtaleCoordinates.toAffineSpace, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The native chart map to the polynomial spectrum is étale.
Source: Hartshorne, Algebraic Geometry, II.8; HodgeConjecture,
AlgebraicGeometry.LocalEtaleCoordinates.coordinateRingHomOnOpen_etale. -/
theorem s2e_native_polynomial_coordinates_etale
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x) :
    Etale (s2e_native_polynomial_coordinates X d x D).left := by
  letI := s2e_native_coordinate_map_etale X d x D
  change Etale (D.toAffineSpace ≫ (AffineSpace.SpecIso (Fin d) ↧ℂ).hom)
  infer_instance

/-- Scalar evaluation of the native polynomial coordinates agrees with
evaluation of their actual regular sections on the affine neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.2; HodgeConjecture,
AlgebraicGeometry.ComplexPoint.affineSpecEquiv_apply. -/
theorem s2e_native_polynomial_coordinates_evaluation
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x)
    (p : ComplexPoint (ComplexPoint.openScheme X D.neighborhood))
    (r : MvPolynomial (Fin d) ℂ) :
    ComplexPoint.affineSpecEquiv (MvPolynomial (Fin d) ℂ)
      (Point.map (s2e_native_polynomial_coordinates X d x D) p) r =
        Point.evaluate ⊤ (D.coordinateRingHomOnOpen r) p := by
  exact s2e_spec_coordinate_evaluation (ComplexPoint.openScheme X D.neighborhood)
    (MvPolynomial (Fin d) ℂ) (s2e_native_polynomial_coordinates X d x D)
    (CommRingCat.ofHom D.coordinateRingHomOnOpen)
    (s2e_native_polynomial_coordinates_left X d x D) p r

/-- The scalar polynomial coordinate of an actual point is its native
analytic coordinate value.
Source: HodgeConjecture,
AlgebraicGeometry.LocalEtaleCoordinates.analyticCoordinates_apply_eq_evaluate. -/
theorem s2e_native_polynomial_coordinate_value
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x)
    (p : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) (i : Fin d) :
    ComplexPoint.affineSpecEquiv (MvPolynomial (Fin d) ℂ)
      (Point.map (s2e_native_polynomial_coordinates X d x D) p) (MvPolynomial.X i) =
        D.analyticCoordinates p i := by
  exact (s2e_native_polynomial_coordinates_evaluation X d x D p (MvPolynomial.X i)).trans
    (D.analyticCoordinates_apply_eq_evaluate p i).symm

end HodgeLean.Foundations.Program
