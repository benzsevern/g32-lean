import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import Mathlib.RingTheory.Polynomial.Quotient

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Setting the literal chart ratio to zero retains the original numerator divisor algebra. -/
def ratioResidualEquiv {R : Type*} [CommRing R] (u v : R) :
    (RegularPairChart.ring u v ⧸ Ideal.span {RegularPairChart.ratio u v}) ≃ₐ[R]
      R ⧸ Ideal.span {u} := by
  let J : Ideal R[X] := Ideal.span {C u - X * C v}
  let K : Ideal R[X] := Ideal.span {X}
  have hmap : K.map (Ideal.Quotient.mk J) =
      Ideal.span {RegularPairChart.ratio u v} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hsup : J ⊔ K = Ideal.span {C u, X - C (0 : R)} := by
    simp only [J, K, ← Ideal.span_union, Set.singleton_union, map_zero, sub_zero]
    rw [sub_eq_add_neg, ← mul_neg, Ideal.span_pair_add_right_mul]
  exact (Ideal.quotientEquivAlgOfEq R hmap.symm).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R J K).trans
      ((Ideal.quotientEquivAlgOfEq R hsup).trans (Polynomial.quotientSpanCXSubCAlgEquiv u 0)))

end AlgebraicGeometry.RamifiedNormalization.StageFour
