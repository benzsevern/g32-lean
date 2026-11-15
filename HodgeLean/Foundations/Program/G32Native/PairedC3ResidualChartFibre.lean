import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualChartCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedResidualSurjectiveFibre

/-! # The base map and the marked fibre of a residual Rees chart -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial AlgebraicGeometry.RegularPairChart
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The original base quotient maps to the residual chart by its coefficient
map, factoring through the actual ideal of D.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
def pairedC3ResidualChartBase {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) :
    A ⧸ J →+* ring u v ⧸ J.map (coeff u v) :=
  Ideal.Quotient.lift J
    ((Ideal.Quotient.mk (J.map (coeff u v))).comp (coeff u v))
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx))

/-- The chart comparison retains the original base coefficients.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem pairedC3_residual_chart_base {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) (x : A ⧸ J) :
    pairedC3ResidualChartEquiv u v J hu hv (pairedC3ResidualChartBase u v J x) = C x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [pairedC3ResidualChartBase, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  simpa only [Polynomial.map_C] using
    pairedC3_residual_chart_polynomial u v J hu hv (C a)

/-- The map specified by the original base coefficients and Rees ratio is
exactly the inverse polynomial chart comparison.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem pairedC3_residual_chart_parameter {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) :
    Polynomial.eval₂RingHom (pairedC3ResidualChartBase u v J)
        (Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v)) =
      (pairedC3ResidualChartEquiv u v J hu hv).symm.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro x
    apply (pairedC3ResidualChartEquiv u v J hu hv).injective
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact (pairedC3_residual_chart_base u v J hu hv x).trans
      ((pairedC3ResidualChartEquiv u v J hu hv).apply_symm_apply (C x)).symm
  · apply (pairedC3ResidualChartEquiv u v J hu hv).injective
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    exact (pairedC3_residual_chart_ratio u v J hu hv).trans
      ((pairedC3ResidualChartEquiv u v J hu hv).apply_symm_apply X).symm

/-- The marked intersection on the first residual chart is the literal
origin fibre of the map given by its original Rees ratio.
Source: Hartshorne, Algebraic Geometry, II.7.13; Schoen,
Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem pairedC3_residual_chart_marked_fibre (A : Type) [CommRing A]
    (u v : A) (J : Ideal A) :
    let B := ring u v ⧸ J.map (coeff u v)
    let r : B := Ideal.Quotient.mk (J.map (coeff u v)) (ratio u v)
    let q := Ideal.Quotient.mk (Ideal.span {r})
    CategoryTheory.IsPullback
      (Spec.map (CommRingCat.ofHom (q.comp (pairedC3ResidualChartBase u v J))))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A ⧸ J))))
      (Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom (pairedC3ResidualChartBase u v J) r))) :=
  residual_polynomial_origin_isPullback (A ⧸ J) _ (pairedC3ResidualChartBase u v J) _

#print axioms pairedC3ResidualChartBase
#print axioms pairedC3_residual_chart_base
#print axioms pairedC3_residual_chart_parameter
#print axioms pairedC3_residual_chart_marked_fibre
end HodgeLean.Foundations.Program.G32Native
