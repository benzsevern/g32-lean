import HodgeLean.Foundations.Program.G32Native.PairedC3AdaptedEquation
import Mathlib.Algebra.Polynomial.Monic

/-! # Regularity of the Rees relation after restriction to the slice

Only the restricted branch parameter needs to be regular. No regular
generating sequence for the ambient slice ideal enters this calculation.
-/
set_option maxHeartbeats 200000
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- A regular restricted branch parameter makes the restricted Rees relation
regular, including over coefficient rings with nilpotents.
Source: Hartshorne, Algebraic Geometry, II.7.13, quotient chart equations. -/
theorem paired_c3_restricted_relation_regular
    {A : Type*} [CommRing A] (u v a : A)
    (hu : u = a * v) (hv : IsSMulRegular A v) :
    IsSMulRegular A[X] (C u - X * C v) := by
  have hc : IsSMulRegular A[X] (C v) := by
    intro p q h
    apply Polynomial.ext
    intro n
    apply hv
    simpa only [smul_eq_mul, coeff_C_mul] using congrArg (fun p : A[X] => p.coeff n) h
  have hx : IsSMulRegular A[X] (X - C a) := (monic_X_sub_C a).isRegular.left
  have he : C u - X * C v = -((X - C a) * C v) := by
    rw [hu, map_mul]
    ring
  intro p q h
  apply hc
  apply hx
  change (X - C a) * (C v * p) = (X - C a) * (C v * q)
  change (C u - X * C v) * p = (C u - X * C v) * q at h
  rw [he, neg_mul, neg_mul, neg_inj, mul_assoc, mul_assoc] at h
  exact h

#print axioms paired_c3_restricted_relation_regular

/-- A relation regular modulo the slice ideal has precisely the expected
intersection with that ideal. This retains multiplicities in the quotient.
Source: Hartshorne, Algebraic Geometry, II.8, conormal base change;
the kernel of the quotient conormal map is this intersection modulo squares. -/
theorem paired_c3_relation_intersection
    {A : Type*} [CommRing A] (I : Ideal A) (r : A)
    (hr : IsSMulRegular (A ⧸ I) r) :
    I ⊓ Ideal.span {r} = Ideal.span {r} * I := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx.2
    have hmem : r * a ∈ I := ha ▸ hx.1
    have haI : a ∈ I := mem_of_isSMulRegular_quotient_of_smul_mem hr hmem
    rw [ha]
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton r)) haI
  · exact le_inf Ideal.mul_le_right Ideal.mul_le_left

#print axioms paired_c3_relation_intersection
end HodgeLean.Foundations.Program.G32Native
