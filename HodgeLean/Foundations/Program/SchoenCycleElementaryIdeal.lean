import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The elementary symmetric ideal and the variable ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Every variable becomes nilpotent modulo the positive elementary symmetric
polynomials, by evaluating its characteristic polynomial.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2;
Vieta's formula. -/
theorem s2e_variable_pow_mem_elementary_ideal
    (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    (X i : MvPolynomial (Fin n) R) ^ n ∈
      Ideal.span (Set.range (fun j : Fin n => esymm (Fin n) R (j.val + 1))) := by
  let J : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range (fun j : Fin n => esymm (Fin n) R (j.val + 1)))
  let q := Ideal.Quotient.mk J
  have he (j : Fin n) : q (esymm (Fin n) R (j.val + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  have h := congrArg (fun p : Polynomial (MvPolynomial (Fin n) R) =>
    Polynomial.eval₂ q (-q (X i)) p) (MvPolynomial.prod_C_add_X_eq_sum_esymm R (Fin n))
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Fintype.card_fin] at h
  have hp : (∏ j : Fin n, (-q (X i) + q (X j))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (neg_add_cancel _)
  rw [hp, Finset.sum_range_succ'] at h
  have hs : (∑ j ∈ Finset.range n, q (esymm (Fin n) R (j + 1)) *
      (-q (X i)) ^ (n - (j + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [he ⟨j, Finset.mem_range.mp hj⟩]
    exact zero_mul _
  rw [hs] at h
  simp only [esymm_zero, map_one, Nat.sub_zero, one_mul, zero_add] at h
  have hz : q (X i) ^ n = 0 := by
    rcases Nat.even_or_odd n with hn | hn
    · simpa only [hn.neg_pow] using h.symm
    · simpa only [hn.neg_pow, neg_eq_zero] using h.symm
  change X i ^ n ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_pow, hz]

#print axioms s2e_variable_pow_mem_elementary_ideal
/-- The variable ideal lies in the radical of the positive elementary
symmetric ideal.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_idealOfVars_le_elementary_radical
    (R : Type*) [CommRing R] (n : ℕ) :
    idealOfVars (Fin n) R ≤
      (Ideal.span (Set.range (fun j : Fin n => esymm (Fin n) R (j.val + 1)))).radical := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨n, s2e_variable_pow_mem_elementary_ideal R n i⟩

#print axioms s2e_idealOfVars_le_elementary_radical
/-- A positive power of the variable ideal is contained in the positive
elementary symmetric ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1;
finite generation and the radical containment from Vieta's formula. -/
theorem s2e_idealOfVars_pow_le_elementary
    (R : Type*) [CommRing R] (n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ idealOfVars (Fin n) R ^ k ≤
      Ideal.span (Set.range (fun j : Fin n => esymm (Fin n) R (j.val + 1))) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (s2e_idealOfVars_le_elementary_radical R n) (idealOfVars_fg (Fin n) R)
  exact ⟨k + 1, Nat.zero_lt_succ k, (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk⟩

#print axioms s2e_idealOfVars_pow_le_elementary
end HodgeLean.Foundations.Program
