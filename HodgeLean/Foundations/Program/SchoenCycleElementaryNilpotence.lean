import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Basic.Complex.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Vanishing elementary coefficients make each individual root nilpotent with the block-size bound.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_elementary_vanishing_root_nilpotence
    {A : Type*} [CommRing A] [Algebra ℂ A] (n : ℕ) (t : Fin n → A)
    (h : ∀ k, 0 < k → k ≤ n → aeval t (esymm (Fin n) ℂ k) = 0)
    (i : Fin n) : t i ^ n = 0 := by
  classical
  let φ : Polynomial (MvPolynomial (Fin n) ℂ) →+* A :=
    Polynomial.eval₂RingHom (aeval t).toRingHom (-t i)
  have he := congrArg φ (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  have hleft : φ (∏ j : Fin n, (Polynomial.X + Polynomial.C (MvPolynomial.X j))) = 0 := by
    simp only [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [φ]
  have hright : φ (∑ j ∈ Finset.range (Fintype.card (Fin n) + 1),
      Polynomial.C (esymm (Fin n) ℂ j) * Polynomial.X ^ (Fintype.card (Fin n) - j)) =
      (-t i) ^ n := by
    simp only [map_sum, map_mul, map_pow, Fintype.card_fin]
    rw [Finset.sum_eq_single 0]
    · simp [φ]
    · intro j hj hj0
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hz := h j (Nat.pos_of_ne_zero hj0) hjn
      simp [φ, hz]
    · simp
  rw [hleft, hright] at he
  have hn : (-t i) ^ n = 0 := he.symm
  have hm := congrArg (fun z : A => (-1 : A) ^ n * z) hn
  simpa only [← mul_pow, neg_one_mul, neg_neg, mul_zero] using hm

#print axioms s2e_elementary_vanishing_root_nilpotence
end HodgeLean.Foundations.Program
