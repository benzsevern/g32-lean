import HodgeLean.Foundations.Program.SchoenCycleNativePolynomialCoordinates
import HodgeLean.Foundations.Program.SchoenCycleAffineLineStalks
import HodgeLean.Foundations.Program.SchoenCycleUnramifiedStalks
import HodgeLean.Foundations.Program.SchoenCycleCoordinateStalkPullback

/-! # Regular stalk parameters from the native curve coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The centered regular section defining a native curve coordinate generates
the actual maximal ideal on its affine coordinate neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8; Stacks Project, Tag 00UW. -/
theorem s2e_native_curve_coordinate_stalk_parameter
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X 1 x)
    (p : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :
    let q := s2e_native_polynomial_coordinates X 1 x D
    let y := Point.map q p
    IsLocalRing.maximalIdeal (D.neighborhood.toScheme.presheaf.stalk p.underlying) =
      Ideal.span (Set.singleton (D.neighborhood.toScheme.presheaf.germ ⊤ p.underlying trivial
        (D.coordinateRingHomOnOpen (MvPolynomial.X 0 - MvPolynomial.C
          (ComplexPoint.affineSpecEquiv (MvPolynomial (Fin 1) ℂ) y (MvPolynomial.X 0)))))) := by
  let P := CommRingCat.of (MvPolynomial (Fin 1) ℂ)
  let q := s2e_native_polynomial_coordinates X 1 x D
  let y := Point.map q p
  let r : MvPolynomial (Fin 1) ℂ := MvPolynomial.X 0 - MvPolynomial.C
    (ComplexPoint.affineSpecEquiv (MvPolynomial (Fin 1) ℂ) y (MvPolynomial.X 0))
  letI : Etale q.left := s2e_native_polynomial_coordinates_etale X 1 x D
  have ht : IsLocalRing.maximalIdeal ((Spec P).presheaf.stalk y.underlying) =
      Ideal.span {(StructureSheaf.toStalk P y.underlying).hom r} :=
    s2e_affine_line_point_stalk_parameter y
  have hu := s2e_unramified_stalk_parameter q.left p.underlying
    ((StructureSheaf.toStalk P y.underlying).hom r) ht
  have he : q.left.stalkMap p.underlying ((StructureSheaf.toStalk P (q.left p.underlying)).hom r) =
      D.neighborhood.toScheme.presheaf.germ ⊤ p.underlying trivial (D.coordinateRingHomOnOpen r) := by
    rw [s2e_native_polynomial_coordinates_left]
    exact s2e_coordinate_stalk_pullback D.neighborhood.toScheme P
      (CommRingCat.ofHom D.coordinateRingHomOnOpen) p.underlying r
  change IsLocalRing.maximalIdeal (D.neighborhood.toScheme.presheaf.stalk p.underlying) =
    Ideal.span {D.neighborhood.toScheme.presheaf.germ ⊤ p.underlying trivial (D.coordinateRingHomOnOpen r)}
  rw [← he]
  exact hu

end HodgeLean.Foundations.Program
