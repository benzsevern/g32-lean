import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Denominator regularity in the two selected blowup charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Multiplication by a regular constant remains injective on the polynomial ring.
Source: the coefficient formula for multiplication by a constant polynomial. -/
theorem s2v_i2b_polynomial_constant_regular
    {R : Type*} [CommRing R] (v : R)
    (hv : Function.Injective (fun a : R => v * a)) :
    Function.Injective (fun p : R[X] => C v * p) := by
  exact (AlgebraicGeometry.RegularPairChart.constant_regular v
    ((Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr hv)).left

/-- A regular selected pair makes its blowup-chart relation saturated in the denominator.
Source: reduction modulo the denominator followed by polynomial cancellation. -/
theorem s2v_i2b_chart_relation_saturated
    {R : Type*} [CommRing R] (u v : R)
    (hv : Function.Injective (fun a : R => v * a))
    (hu : Function.Injective (fun a : R ⧸ Ideal.span {v} =>
      Ideal.Quotient.mk (Ideal.span {v}) u * a))
    (p : R[X]) (hp : C v * p ∈ Ideal.span {C u - X * C v}) :
    p ∈ Ideal.span {C u - X * C v} := by
  apply Ideal.mem_span_singleton.mpr
  exact AlgebraicGeometry.RegularPairChart.relation_saturated u v
    ((Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr hv)
    ((Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr hu) p
    (Ideal.mem_span_singleton.mp hp)

/-- The denominator is a regular element in the selected algebraic blowup chart.
Source: saturation of the chart relation by the denominator. -/
theorem s2v_i2b_chart_denominator_regular
    {R : Type*} [CommRing R] (u v : R)
    (hv : Function.Injective (fun a : R => v * a))
    (hu : Function.Injective (fun a : R ⧸ Ideal.span {v} =>
      Ideal.Quotient.mk (Ideal.span {v}) u * a)) :
    Function.Injective (fun a : R[X] ⧸ Ideal.span {C u - X * C v} =>
      Ideal.Quotient.mk (Ideal.span {C u - X * C v}) (C v) * a) := by
  let q : R[X] →+* R[X] ⧸ Ideal.span {C u - X * C v} := Ideal.Quotient.mk _
  intro a b hab
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem p r).mpr
  apply s2v_i2b_chart_relation_saturated u v hv hu
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (C v * (p - r)) = 0
  rw [map_mul, map_sub, mul_sub]
  exact sub_eq_zero.mpr hab

/-- The chart relation remains saturated in the denominator after imposing an independent branch.
Source: reduction by the unpaired branch equation and saturation of the selected pair. -/
theorem s2v_i2b_chart_relation_saturated_mod_branch
    {R : Type*} [CommRing R] (u v z : R)
    (hv : Function.Injective (fun a : R ⧸ Ideal.span {z} =>
      Ideal.Quotient.mk (Ideal.span {z}) v * a))
    (hu : Function.Injective (fun a : (R ⧸ Ideal.span {z}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {z}) v} =>
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {z}) v})
        (Ideal.Quotient.mk (Ideal.span {z}) u) * a))
    (p : R[X])
    (hp : C v * p ∈ Ideal.span {C u - X * C v} ⊔ Ideal.span {C z}) :
    p ∈ Ideal.span {C u - X * C v} ⊔ Ideal.span {C z} := by
  let π : R →+* R ⧸ Ideal.span {z} := Ideal.Quotient.mk _
  let φ := Polynomial.mapRingHom π
  let I : Ideal R[X] := Ideal.span {C u - X * C v} ⊔ Ideal.span {C z}
  have hπz : π z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton z))
  have hF : (C u - X * C v).map π = C (π u) - X * C (π v) := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C]
  have hφI : Ideal.map φ I = Ideal.span {C (π u) - X * C (π v)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    simp only [φ, coe_mapRingHom, hF, Polynomial.map_C, hπz, Polynomial.C_0,
      Ideal.span_singleton_zero, sup_bot_eq]
  have hpre : C (π v) * p.map π ∈ Ideal.span {C (π u) - X * C (π v)} := by
    have hmem : φ (C v * p) ∈ Ideal.map φ I := Ideal.mem_map_of_mem φ hp
    rw [hφI] at hmem
    simpa only [φ, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C] using hmem
  have hsat := s2v_i2b_chart_relation_saturated (π u) (π v) hv hu (p.map π) hpre
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hsat
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (f := π) Ideal.Quotient.mk_surjective s
  have hkernel : (p - (C u - X * C v) * r).map π = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hF, hr, ← hs, sub_self]
  have hrem : p - (C u - X * C v) * r ∈ Ideal.span {C z} := by
    apply Ideal.mem_span_singleton.mpr
    apply (C_dvd_iff_dvd_coeff z _).mpr
    intro n
    have hn : π ((p - (C u - X * C v) * r).coeff n) = 0 := by
      simpa only [coeff_map, coeff_zero] using congrArg (fun f => f.coeff n) hkernel
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hn)
  have h1 : (C u - X * C v) * r ∈ I :=
    Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨r, rfl⟩)
  have h2 : p - (C u - X * C v) * r ∈ I := Ideal.mem_sup_right hrem
  simpa only [sub_add_cancel] using I.add_mem h2 h1

/-- Saturation by an element gives injective multiplication on the quotient.
Source: the quotient equality criterion applied to the difference of representatives. -/
theorem s2v_i2b_quotient_regular_of_saturated
    {R : Type*} [CommRing R] (I : Ideal R) (v : R)
    (h : ∀ a : R, v * a ∈ I → a ∈ I) :
    Function.Injective (fun a : R ⧸ I => Ideal.Quotient.mk I v * a) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr
  apply h
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_mul, map_sub, mul_sub]
  exact sub_eq_zero.mpr hab

end HodgeLean.Foundations.Program
