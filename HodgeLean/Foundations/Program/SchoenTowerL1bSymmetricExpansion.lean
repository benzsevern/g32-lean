import HodgeLean.Foundations.Program.SchoenTowerL1bBranchPolynomial
import Mathlib.RingTheory.Polynomial.Vieta

/-! Symmetric expansion of the retained branch polynomial.
HC no distance; AV milestone no distance. -/

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Evaluation of the ordered product is the symmetric coefficient expansion with its actual sign. -/
theorem s2v_l1b_ordered_product_expansion
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (n : ℕ) (z : Fin n → A) (a : A) :
    (∏ i, (z i - a)) = ∑ j ∈ Finset.range (n + 1),
      MvPolynomial.aeval (R := K) z (MvPolynomial.esymm (Fin n) K j) *
        (-a) ^ (n - j) := by
  classical
  have H := congrArg (fun P : Polynomial (MvPolynomial (Fin n) K) =>
    Polynomial.eval₂ (MvPolynomial.aeval (R := K) z).toRingHom (-a) P)
    (MvPolynomial.prod_C_add_X_eq_sum_esymm K (Fin n))
  simpa only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_C, MvPolynomial.aeval_X,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Fintype.card_fin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, sub_eq_add_neg, add_comm (-a)] using H

/-- The actual descended polynomial evaluates in the same descended coefficient sections. -/
theorem s2v_l1b_descended_product_expansion
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (n : ℕ) (z : Fin n → B) (q : A →ₐ[K] B)
    (hq : Function.Injective q) (P : Polynomial A)
    (hP : P.map q.toRingHom = ∏ i, (Polynomial.C (z i) - Polynomial.X))
    (c : Fin n → A)
    (hc : ∀ j, q (c j) =
      MvPolynomial.aeval (R := K) z (MvPolynomial.esymm (Fin n) K (j.val + 1)))
    (a : K) :
    P.eval (algebraMap K A a) = (-algebraMap K A a) ^ n +
      ∑ j : Fin n, c j * (-algebraMap K A a) ^ (n - (j.val + 1)) := by
  apply hq
  change q.toRingHom (P.eval (algebraMap K A a)) = _
  rw [s2v_l1b_branch_polynomial_eval n z q.toRingHom P hP]
  change (∏ i, (z i - q (algebraMap K A a))) = _
  simp only [map_add, map_pow, map_neg, map_sum, map_mul, q.commutes, hc]
  rw [s2v_l1b_ordered_product_expansion (K := K)]
  rw [Finset.sum_range_succ']
  simp only [MvPolynomial.esymm_zero, map_one, one_mul, Nat.sub_zero]
  rw [add_comm]
  congr 1
  exact (Fin.sum_univ_eq_sum_range _ n).symm

end HodgeLean.Foundations.Program
