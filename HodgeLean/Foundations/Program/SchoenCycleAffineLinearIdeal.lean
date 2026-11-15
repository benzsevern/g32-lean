import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Reduced affine linear equations -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A nonconstant affine linear equation generates a prime ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, I.1. -/
theorem s2e_affine_linear_polynomial_isPrime
    {n : ℕ} (a : Fin n → ℂ) (c : ℂ) (ha : a ≠ 0) :
    (Ideal.span ({C c + ∑ i, C (a i) * X i} : Set (MvPolynomial (Fin n) ℂ))).IsPrime := by
  classical
  let p : MvPolynomial (Fin n) ℂ := C c + ∑ i, C (a i) * X i
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  have hm : (0 : Fin n →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro he
    have he' := congrArg (fun t : Fin n →₀ ℕ => t i) he
    simpa using he'
  have hcoeff : p.coeff (Finsupp.single i 1) = a i := by
    simp [p, coeff_C, coeff_X, Finsupp.single_left_inj Nat.one_ne_zero, hm]
  have hle : p.totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply totalDegree_finsetSum_le
      intro j hj
      exact (totalDegree_mul _ _).trans (by simp)
  have hdeg : p.totalDegree = 1 := by
    apply Nat.le_antisymm hle
    by_contra! h
    have hc := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (by omega : p.totalDegree ≤ 0))
    have he := congrArg (fun q : MvPolynomial (Fin n) ℂ => q.coeff (Finsupp.single i 1)) hc
    rw [hcoeff] at he
    exact hi (by simpa [hm] using he)
  have hirr : Irreducible p := by
    apply irreducible_of_totalDegree_eq_one hdeg
    intro r hr
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hd := hr (Finsupp.single i 1)
    rw [hzero, hcoeff, zero_dvd_iff] at hd
    exact hi hd
  exact (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime

/-- The actual affine linear zero set has its linear principal vanishing ideal, with multiplicity one.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, I.1. -/
theorem s2e_affine_linear_vanishingIdeal
    {n : ℕ} (a : Fin n → ℂ) (c : ℂ) :
    MvPolynomial.vanishingIdeal ℂ
      {x : Fin n → ℂ | c + ∑ i, a i * x i = 0} =
      Ideal.span ({C c + ∑ i, C (a i) * X i} : Set (MvPolynomial (Fin n) ℂ)) := by
  classical
  let F : MvPolynomial (Fin n) ℂ := C c + ∑ i, C (a i) * X i
  have hzero : MvPolynomial.zeroLocus ℂ (Ideal.span {F}) =
      {x : Fin n → ℂ | c + ∑ i, a i * x i = 0} := by
    ext x
    constructor
    · intro hx
      simpa [F] using hx F (Ideal.subset_span (Set.mem_singleton F))
    · intro hx q hq
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hq
      simp [F, show c + ∑ i, a i * x i = 0 from hx]
  have hrad : (Ideal.span ({F} : Set (MvPolynomial (Fin n) ℂ))).IsRadical := by
    by_cases ha : a = 0
    · subst a
      dsimp only [F]
      simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
      by_cases hc : c = 0
      · subst c
        simpa using (Ideal.isRadical_bot :
          (⊥ : Ideal (MvPolynomial (Fin n) ℂ)).IsRadical)
      · have hu : IsUnit (C c : MvPolynomial (Fin n) ℂ) :=
          (isUnit_iff_ne_zero.mpr hc).map C
        rw [Ideal.span_singleton_eq_top.mpr hu]
        exact fun _ _ => Submodule.mem_top
    · exact (s2e_affine_linear_polynomial_isPrime a c ha).isRadical
  rw [← hzero]
  exact (MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (Ideal.span {F})).trans hrad.radical

end HodgeLean.Foundations.Program
