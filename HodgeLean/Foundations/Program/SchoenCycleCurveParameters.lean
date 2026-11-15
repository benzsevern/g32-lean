import HodgeLean.Foundations.Program.SchoenCycleNativeCurveParameter

/-! # A point-indexed choice of actual regular curve parameters -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Use the native regular parameter as a function of the actual curve point, so
repeated occurrences of that point use the same parameter.
Source: Hartshorne, Algebraic Geometry, II.8, smooth curve local rings. -/
def s2e_curvePointParameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (p : ComplexPoint X) : X.left.presheaf.stalk p.underlying :=
  s2e_native_curve_parameter X p

/-- The point-indexed curve parameter is irreducible in the actual stalk.
Source: Hartshorne, Algebraic Geometry, II.8, smooth curve local rings. -/
theorem s2e_curvePointParameter_irreducible
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (p : ComplexPoint X) : Irreducible (s2e_curvePointParameter X p) :=
  s2e_native_curve_parameter_irreducible X p

/-- The point-indexed curve parameter generates its actual maximal ideal.
Source: Hartshorne, Algebraic Geometry, II.8, smooth curve local rings. -/
theorem s2e_curvePointParameter_maximalIdeal
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (p : ComplexPoint X) :
    IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) =
      Ideal.span {s2e_curvePointParameter X p} :=
  s2e_native_curve_parameter_maximalIdeal X p

/-- Equal actual curve points have the same chosen parameter after stalk transport.
Source: Hartshorne, Algebraic Geometry, II.2, stalk transport. -/
theorem s2e_curvePointParameter_congr
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (p q : ComplexPoint X) (h : p = q) :
    (X.left.presheaf.stalkCongr (.of_eq (congrArg Point.underlying h))).hom
      (s2e_curvePointParameter X p) = s2e_curvePointParameter X q := by
  subst q
  simp

end HodgeLean.Foundations.Program
