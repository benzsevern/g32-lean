import HodgeLean.Foundations.Program.SchoenCycleNativeCenteredSections
import HodgeLean.Foundations.Program.SchoenCycleCurveStalkJets

/-! # The regular parameter underlying the chosen native curve chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual stalk germ of the centered regular coordinate from the native
analytic chart chosen at the specified curve point.
Source: Hartshorne, Algebraic Geometry, II.8; HodgeConjecture,
AlgebraicGeometry.localEtaleCoordinates. -/
def s2e_native_curve_parameter
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X) :
    X.left.presheaf.stalk p.underlying := by
  let D := localEtaleCoordinates X 1 p.underlying
  let pU := ComplexPoint.asOpenPoint X D.neighborhood p D.mem
  have hp : p.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using D.mem
  exact X.left.presheaf.germ D.ambientCoordinateOpen p.underlying hp
    (s2e_native_ambient_centered_section X p.underlying D pU)

/-- The parameter from the chosen native chart generates the actual curve
point's maximal ideal.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_native_curve_parameter_maximalIdeal
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X) :
    IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) =
      Ideal.span {s2e_native_curve_parameter X p} := by
  let D := localEtaleCoordinates X 1 p.underlying
  let pU := ComplexPoint.asOpenPoint X D.neighborhood p D.mem
  have hp : p.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using D.mem
  have hmap : Point.map (ComplexPoint.openInclusion X D.neighborhood) pU = p := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X D.neighborhood p D.mem
  have hpoint : D.neighborhood.ι pU.underlying = p.underlying := by
    have h := congrArg Point.underlying hmap
    rw [Point.underlying_map] at h
    exact h
  have hpU : D.neighborhood.ι pU.underlying ∈ D.ambientCoordinateOpen := by
    rwa [hpoint]
  have h := s2e_native_ambient_centered_section_parameter X p.underlying D pU hpU
  exact s2e_section_parameter_point_congr X.left D.ambientCoordinateOpen
    (D.neighborhood.ι pU.underlying) p.underlying hpU hp hpoint
    (s2e_native_ambient_centered_section X p.underlying D pU) h

/-- The point-indexed native parameter is irreducible in the actual stalk of
the smooth projective curve.
Source: Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald,
Introduction to Commutative Algebra, Chapter 9. -/
theorem s2e_native_curve_parameter_irreducible
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X) :
    Irreducible (s2e_native_curve_parameter X p) := by
  letI : IsDiscreteValuationRing (X.left.presheaf.stalk p.underlying) :=
    s2e_smooth_curve_point_stalk_dvr X p
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (s2e_native_curve_parameter_maximalIdeal X p)

end HodgeLean.Foundations.Program
