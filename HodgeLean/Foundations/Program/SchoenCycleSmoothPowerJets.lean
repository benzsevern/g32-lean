import HodgeLean.Foundations.Program.SchoenCycleProductJetAlgebra
import HodgeLean.Foundations.Program.SchoenCycleCurveParameters
import HodgeLean.Foundations.GeometricIntegralityC

/-! # Consistent finite coordinates on powers of the actual smooth curve -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Pull the point-indexed regular curve parameters back along the actual
curve-power projections.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
def s2e_curvePowerParameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) (i : Fin n) :
    (g3_power X n).left.presheaf.stalk x.underlying :=
  (g3_proj X n i).left.stalkMap x.underlying
    (s2e_curvePointParameter X (Point.map (g3_proj X n i) x))

/-- Every positive-order infinitesimal neighbourhood on an actual smooth curve
power has the specified polynomial coordinates, chosen consistently at repeated points.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_smooth_curve_power_stalk_finite_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) (N : ℕ) (hN : 0 < N) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ e : (MvPolynomial (Fin n) ℂ ⧸ idealOfVars (Fin n) ℂ ^ N) ≃ₐ[ℂ]
        (R ⧸ IsLocalRing.maximalIdeal R ^ N),
      ∀ p : MvPolynomial (Fin n) ℂ,
        e (Ideal.Quotient.mk (idealOfVars (Fin n) ℂ ^ N) p) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)
            (aeval (s2e_curvePowerParameter X n x) p) := by
  let t (i : Fin n) : X.left.presheaf.stalk ((g3_proj X n i).left x.underlying) :=
    s2e_curvePointParameter X (Point.map (g3_proj X n i) x)
  have ht (i : Fin n) : IsLocalRing.maximalIdeal
      (X.left.presheaf.stalk ((g3_proj X n i).left x.underlying)) = Ideal.span {t i} :=
    s2e_curvePointParameter_maximalIdeal X (Point.map (g3_proj X n i) x)
  have hreg (i : Fin n) : Function.Injective (fun z => t i * z) := by
    intro a b hab
    exact mul_left_cancel₀
      (s2e_curvePointParameter_irreducible X (Point.map (g3_proj X n i) x)).ne_zero hab
  exact s2e_curve_power_stalk_total_jet_coordinates X n x t ht hreg N hN

end HodgeLean.Foundations.Program
