import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartDefs
import Mathlib.RingTheory.Polynomial.Basic

/-! # The residual affine line in a two-generator Rees chart

Setting the ideal of the base D to zero removes the binomial relation.
The ratio remains the polynomial coordinate, including its marked origin.
-/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native

/-- Over a subscheme of the centre, the binomial relation belongs to the
extended base ideal.
Source: Hartshorne, Algebraic Geometry, II.7.13, affine blow-up charts. -/
theorem pairedC3_chart_relation_le {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) :
    Ideal.span {C u - X * C v} ≤ J.map (C : A →+* A[X]) := by
  apply Ideal.span_le.mpr
  rintro p (rfl : p = C u - X * C v)
  exact sub_mem (Ideal.mem_map_of_mem _ hu)
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hv))

/-- The actual residual quotient of a binomial Rees chart is a polynomial
ring over the original base quotient.
Source: Hartshorne, Algebraic Geometry, II.7.13; Fulton,
Intersection Theory, B.6. -/
def pairedC3ResidualChartEquiv {A : Type*} [CommRing A]
    (u v : A) (J : Ideal A) (hu : u ∈ J) (hv : v ∈ J) :
    (ring u v ⧸ J.map (coeff u v)) ≃+* (A ⧸ J)[X] := by
  let Q : Ideal A[X] := Ideal.span {C u - X * C v}
  have hQ : Q ⊔ J.map C = J.map C :=
    sup_eq_right.mpr (pairedC3_chart_relation_le u v J hu hv)
  have hk : RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk J)) = J.map C := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  have hs : Function.Surjective (Polynomial.mapRingHom (Ideal.Quotient.mk J)) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  change (A[X] ⧸ Q) ⧸ J.map ((Ideal.Quotient.mk Q).comp C) ≃+* _
  exact (Ideal.quotEquivOfEq (show (J.map C).map (Ideal.Quotient.mk Q) = J.map ((Ideal.Quotient.mk Q).comp C) from Ideal.map_map _ _).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup Q (J.map C)).trans
      ((Ideal.quotEquivOfEq hQ).trans
        ((Ideal.quotEquivOfEq hk.symm).trans
          (RingHom.quotientKerEquivOfSurjective hs))))

#print axioms pairedC3_chart_relation_le
#print axioms pairedC3ResidualChartEquiv
end HodgeLean.Foundations.Program.G32Native
