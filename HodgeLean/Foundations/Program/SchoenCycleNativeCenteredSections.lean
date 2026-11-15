import HodgeLean.Foundations.Program.SchoenCycleNativeCurveStalks
import HodgeLean.Foundations.Program.SchoenCycleOpenStalkSections

/-! # Centered native curve coordinates as actual regular sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The regular section defining the native curve coordinate centered at an
actual point of its affine chart.
Source: Hartshorne, Algebraic Geometry, II.8; HodgeConjecture,
AlgebraicGeometry.LocalEtaleCoordinates.analyticCoordinates. -/
def s2e_native_curve_centered_section
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X 1 x)
    (p : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :
    Γ(D.neighborhood.toScheme, ⊤) :=
  D.coordinateRingHomOnOpen (MvPolynomial.X 0 - MvPolynomial.C (D.analyticCoordinates p 0))

/-- The centered native regular section generates the actual maximal ideal
at its reference point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8; Stacks Project, Tag 00UW. -/
theorem s2e_native_centered_section_parameter
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X 1 x)
    (p : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :
    IsLocalRing.maximalIdeal (D.neighborhood.toScheme.presheaf.stalk p.underlying) =
      Ideal.span (Set.singleton (D.neighborhood.toScheme.presheaf.germ ⊤ p.underlying trivial
        (s2e_native_curve_centered_section X x D p))) := by
  have h := s2e_native_curve_coordinate_stalk_parameter X x D p
  dsimp only at h
  rw [s2e_native_polynomial_coordinate_value X 1 x D p 0] at h
  exact h

/-- Evaluation of the centered regular section is exactly the difference of
native analytic coordinate values.
Source: HodgeConjecture,
AlgebraicGeometry.LocalEtaleCoordinates.analyticCoordinates_apply_eq_evaluate. -/
theorem s2e_native_centered_section_evaluate
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X 1 x)
    (p q : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :
    Point.evaluate ⊤ (s2e_native_curve_centered_section X x D p) q =
      D.analyticCoordinates q 0 - D.analyticCoordinates p 0 := by
  let f := s2e_native_polynomial_coordinates X 1 x D
  let ψ := ComplexPoint.affineSpecEquiv (MvPolynomial (Fin 1) ℂ) (Point.map f q)
  let c := D.analyticCoordinates p 0
  have hc : ψ (MvPolynomial.C c) = c := by
    simpa only [MvPolynomial.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply] using ψ.commutes c
  have hv : ψ (MvPolynomial.X 0) = D.analyticCoordinates q 0 :=
    s2e_native_polynomial_coordinate_value X 1 x D q 0
  change Point.evaluate ⊤ (D.coordinateRingHomOnOpen (MvPolynomial.X 0 - MvPolynomial.C c)) q = _
  rw [← s2e_native_polynomial_coordinates_evaluation X 1 x D q
    (MvPolynomial.X 0 - MvPolynomial.C c)]
  change ψ (MvPolynomial.X 0 - MvPolynomial.C c) = _
  rw [map_sub, hc, hv]

/-- Transport the centered native regular coordinate to its actual ambient open.
Source: Hartshorne, Algebraic Geometry, II.2, open subschemes and regular sections. -/
def s2e_native_ambient_centered_section
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X 1 x)
    (p : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :
    Γ(X.left, D.ambientCoordinateOpen) :=
  (D.neighborhood.ι.appIso ⊤).inv (s2e_native_curve_centered_section X x D p)

/-- The ambient centered native regular section generates the actual maximal
ideal at the image of its reference point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_native_ambient_centered_section_parameter
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X 1 x)
    (p : ComplexPoint (ComplexPoint.openScheme X D.neighborhood))
    (hp : D.neighborhood.ι p.underlying ∈ D.ambientCoordinateOpen) :
    IsLocalRing.maximalIdeal (X.left.presheaf.stalk (D.neighborhood.ι p.underlying)) =
      Ideal.span (Set.singleton (X.left.presheaf.germ D.ambientCoordinateOpen
        (D.neighborhood.ι p.underlying) hp (s2e_native_ambient_centered_section X x D p))) := by
  exact s2e_open_ambient_stalk_parameter X.left D.neighborhood p.underlying hp
    (s2e_native_curve_centered_section X x D p) (s2e_native_centered_section_parameter X x D p)

/-- The transported ambient section still evaluates to the centered native
coordinate on actual points of the affine chart.
Source: HodgeConjecture, AlgebraicGeometry.ComplexPoint.evaluate_openEquiv. -/
theorem s2e_native_ambient_centered_section_evaluate
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X 1 x)
    (p q : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :
    Point.evaluate D.ambientCoordinateOpen (s2e_native_ambient_centered_section X x D p)
      (Point.map (ComplexPoint.openInclusion X D.neighborhood) q) =
        D.analyticCoordinates q 0 - D.analyticCoordinates p 0 := by
  change Point.evaluate (D.neighborhood.ι ''ᵁ ⊤)
    ((D.neighborhood.ι.appIso ⊤).inv (s2e_native_curve_centered_section X x D p))
      (Point.map (ComplexPoint.openInclusion X D.neighborhood) q) = _
  rw [ComplexPoint.evaluate_openEquiv]
  exact s2e_native_centered_section_evaluate X x D p q

end HodgeLean.Foundations.Program
