import HodgeLean.Foundations.Program.SchoenTowerI2aBranchCoordinates
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Descending branch equations through polynomial coefficients
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A product of linear branch factors is the evaluation of its monic coefficient polynomial.
Source: Mathlib, Polynomial.eval_eq_sum_range and Polynomial.monic_prod_X_sub_C. -/
theorem s2v_i2a_branch_product_coefficient_evaluation
    {B : Type*} [CommRing B] [Nontrivial B] (n : ℕ) (z : Fin n → B) (b : B) :
    ∏ i, (b - z i) = b ^ n + ∑ j : Fin n,
      (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff (j : ℕ) * b ^ (j : ℕ) := by
  let P : Polynomial B := ∏ i, (Polynomial.X - Polynomial.C (z i))
  have hdeg : P.natDegree = n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card Finset.univ z
  have hmonic : P.Monic := Polynomial.monic_prod_X_sub_C z Finset.univ
  have hcoeff : P.coeff n = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  calc
    ∏ i, (b - z i) = P.eval b := by simp [P, Polynomial.eval_prod]
    _ = (∑ j ∈ Finset.range n, P.coeff j * b ^ j) + P.coeff n * b ^ n := by
      rw [Polynomial.eval_eq_sum_range, hdeg, Finset.sum_range_succ]
    _ = b ^ n + ∑ j : Fin n, P.coeff (j : ℕ) * b ^ (j : ℕ) := by
      rw [hcoeff, one_mul, add_comm]
      exact congrArg (fun t => b ^ n + t)
        (Fin.sum_univ_eq_sum_range (fun j => P.coeff j * b ^ j) n).symm

/-- The monic coefficient chart descends each branch-factor product to its polynomial evaluation function.
Source: Mathlib, algebra homomorphism functoriality and monic polynomial evaluation. -/
theorem s2v_i2a_descended_branch_evaluation
    {k D B : Type*} [CommRing k] [CommRing D] [CommRing B] [Nontrivial B]
    [Algebra k D] [Algebra k B] (n : ℕ)
    (c : MvPolynomial (Fin n) k →ₐ[k] D) (q : D →ₐ[k] B) (z : Fin n → B)
    (hc : ∀ j, q (c (MvPolynomial.X j)) =
      (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff (j : ℕ)) (b : k) :
    q (c (MvPolynomial.C (b ^ n) +
      ∑ j : Fin n, MvPolynomial.C (b ^ (j : ℕ)) * MvPolynomial.X j)) =
      ∏ i, (algebraMap k B b - z i) := by
  let f := q.comp c
  have hC (a : k) : f (MvPolynomial.C a) = algebraMap k B a := f.commutes a
  have hX (j : Fin n) : f (MvPolynomial.X j) =
      (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff (j : ℕ) := hc j
  change f (MvPolynomial.C (b ^ n) +
    ∑ j : Fin n, MvPolynomial.C (b ^ (j : ℕ)) * MvPolynomial.X j) = _
  rw [s2v_i2a_branch_product_coefficient_evaluation]
  simp only [map_add, map_sum, map_mul, hC, hX, map_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end HodgeLean.Foundations.Program
