import HodgeLean.Foundations.Program.G32Native.PairedResidualChartExceptionalQuotient
import HodgeLean.Foundations.Program.G32Native.PairedResidualNodeChart

/-! # The residual union equation in every regular-pair quotient chart -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native.FibreC

/-- The original difference fibre is the literal union of the shifted-ratio and exceptional ideals. -/
theorem residual_chart_difference_fibre_ideal {R : Type*} [CommRing R] (u v : R) :
    Ideal.span {coeff u v (u - v)} =
      Ideal.span {ratio u v - 1} ⊓ Ideal.span {coeff u v v} := by
  obtain ⟨f, hk, hX, _⟩ := residual_chart_exceptional_quotient u v
  have hreg : IsRegular ((X : Polynomial (R ⧸ Ideal.span {u, v})) - 1) := by
    simpa only [C_1] using (monic_X_sub_C (1 : R ⧸ Ideal.span {u, v})).isRegular
  have h := residual_principal_inf_kernel f (ratio u v - 1) (by
    intro a ha
    have hz : (X - 1) * a = 0 := by
      simpa only [map_sub, hX, map_one] using ha
    exact hreg.left (hz.trans (mul_zero _).symm))
  rw [hk, Ideal.span_singleton_mul_span_singleton] at h
  have he : (ratio u v - 1) * coeff u v v = coeff u v (u - v) := by
    rw [map_sub, residual_chart_relation]
    ring
  rw [he] at h
  exact h.symm

/-- A retained chart isomorphism transports the actual fibre equation and both component ideals. -/
theorem residual_chart_difference_fibre_transport
    {R A : Type*} [CommRing R] [CommRing A] (u v : R)
    (e : ring u v ≃+* A) (f : R →+* A) (hf : e.toRingHom.comp (coeff u v) = f) :
    Ideal.span {f (u - v)} = Ideal.span {e (ratio u v - 1)} ⊓ Ideal.span {f v} := by
  let E := e.idealComapOrderIso.symm
  have h := congrArg E (residual_chart_difference_fibre_ideal u v)
  rw [OrderIso.map_inf] at h
  change (Ideal.span {coeff u v (u - v)}).map e.toRingHom =
    (Ideal.span {ratio u v - 1}).map e.toRingHom ⊓
      (Ideal.span {coeff u v v}).map e.toRingHom at h
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton] at h
  have hc (r : R) : e.toRingHom (coeff u v r) = f r := DFunLike.congr_fun hf r
  rw [hc, hc] at h
  exact h

#print axioms residual_chart_difference_fibre_transport
#print axioms residual_chart_difference_fibre_ideal
end HodgeLean.Foundations.Program.G32Native.FibreC
