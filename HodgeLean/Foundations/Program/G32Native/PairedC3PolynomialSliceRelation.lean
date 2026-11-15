import HodgeLean.Foundations.Program.G32Native.PairedC3RestrictedRelation
import Mathlib.RingTheory.Polynomial.Quotient

/-! # The chart relation modulo the extended ambient slice ideal -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- An adapted branch equation in the actual slice ideal and a regular
restricted branch parameter make the Rees relation regular modulo the
polynomial extension of the entire slice ideal.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_polynomial_slice_relation_regular
    {A : Type*} [CommRing A] (I : Ideal A) (u v a : A)
    (ha : u - a * v ∈ I) (hv : IsSMulRegular (A ⧸ I) v) :
    IsSMulRegular (A[X] ⧸ I.map C) (C u - X * C v) := by
  let q := Ideal.Quotient.mk I
  let e := I.polynomialQuotientEquivQuotientPolynomial.symm
  have hu : q u = q a * q v := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rwa [map_sub, map_mul, sub_eq_zero] at h
  have hv' : IsSMulRegular (A ⧸ I) (q v) := by
    intro x y h
    apply hv
    exact h
  have hr := paired_c3_restricted_relation_regular (q u) (q v) (q a) hu hv'
  have he : e (Ideal.Quotient.mk (I.map C) (C u - X * C v)) =
      C (q u) - X * C (q v) := by
    rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk]
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, map_X]
    rfl
  intro x y h
  apply e.injective
  apply hr
  have h' := congrArg e h
  change e (Ideal.Quotient.mk (I.map C) (C u - X * C v) * x) =
    e (Ideal.Quotient.mk (I.map C) (C u - X * C v) * y) at h'
  rwa [map_mul, map_mul, he] at h'

#print axioms paired_c3_polynomial_slice_relation_regular
end HodgeLean.Foundations.Program.G32Native
