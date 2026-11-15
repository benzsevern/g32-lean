import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualChart

/-! # The ratio and marked ideal in the residual affine chart -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native

/-- The residual chart comparison retains every polynomial representative.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem pairedC3_residual_chart_polynomial {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) (p : A[X]) :
    pairedC3ResidualChartEquiv u v J hu hv
        (Ideal.Quotient.mk (J.map (coeff u v))
          (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) p)) =
      p.map (Ideal.Quotient.mk J) := by
  rfl

/-- The retained Rees ratio is exactly the affine-line coordinate after
restricting to D; in particular no translation or inversion occurs.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem pairedC3_residual_chart_ratio {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) :
    pairedC3ResidualChartEquiv u v J hu hv
        (Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v)) =
      (X : (A ⧸ J)[X]) := by
  simpa only [Polynomial.map_X] using pairedC3_residual_chart_polynomial u v J hu hv X

/-- The first-chart marked ideal maps to the literal origin ideal.
Source: Hartshorne, Algebraic Geometry, II.7.13; Schoen,
Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem pairedC3_residual_chart_marked_ideal {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) :
    Ideal.map (pairedC3ResidualChartEquiv u v J hu hv).toRingHom
        (Ideal.span {Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v)}) =
      Ideal.span {(X : (A ⧸ J)[X])} := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun x => Ideal.span {x}) (pairedC3_residual_chart_ratio u v J hu hv)

#print axioms pairedC3_residual_chart_polynomial
#print axioms pairedC3_residual_chart_ratio
#print axioms pairedC3_residual_chart_marked_ideal
end HodgeLean.Foundations.Program.G32Native
