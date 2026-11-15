import HodgeLean.Foundations.Program.SchoenTowerL1bCoefficientCoordinates
import Mathlib.Algebra.Polynomial.Monic

/-! Polynomial evaluations as two coordinates, retaining all higher coefficients.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open scoped BigOperators

/-- Two distinct evaluations of a monic polynomial replace its constant and linear coefficients in an etale map. -/
theorem s2v_l1b_polynomial_evaluation_etale
    {R A : Type} [CommRing R] [CommRing A]
    (n : ℕ) (f : R →+* A) (z : Fin 2 ⊕ Fin n → A)
    (a b : R) (hab : IsUnit (b - a))
    (hEt : (MvPolynomial.eval₂Hom f z).Etale) :
    let P : Polynomial A := Polynomial.X ^ (n + 2) +
      Polynomial.C (z (Sum.inl 0)) +
      Polynomial.C (z (Sum.inl 1)) * Polynomial.X +
      ∑ k : Fin n, Polynomial.C (z (Sum.inr k)) * Polynomial.X ^ (k.val + 2)
    (MvPolynomial.eval₂Hom f (Sum.elim ![P.eval (f a), P.eval (f b)]
      (fun k => z (Sum.inr k)))).Etale := by
  classical
  let r (t : R) : MvPolynomial (Fin n) R :=
    MvPolynomial.C (t ^ (n + 2)) +
      ∑ k : Fin n, MvPolynomial.X k * MvPolynomial.C (t ^ (k.val + 2))
  have hr (t : R) :
      MvPolynomial.eval₂Hom f (fun k => z (Sum.inr k)) (r t) =
        f t ^ (n + 2) + ∑ k : Fin n, z (Sum.inr k) * f t ^ (k.val + 2) := by
    simp only [r, map_add, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', map_pow]
  have H := s2v_l1b_two_evaluation_all_etale f z a b (r a) (r b) hab hEt
  let P : Polynomial A := Polynomial.X ^ (n + 2) +
    Polynomial.C (z (Sum.inl 0)) + Polynomial.C (z (Sum.inl 1)) * Polynomial.X +
    ∑ k : Fin n, Polynomial.C (z (Sum.inr k)) * Polynomial.X ^ (k.val + 2)
  have hev (t : R) : P.eval (f t) = z (Sum.inl 0) + f t * z (Sum.inl 1) +
      MvPolynomial.eval₂Hom f (fun k => z (Sum.inr k)) (r t) := by
    simp only [P, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_finsetSum, hr]
    ring
  change (MvPolynomial.eval₂Hom f (Sum.elim ![P.eval (f a), P.eval (f b)]
    (fun k => z (Sum.inr k)))).Etale
  simpa only [hev] using H

/-- The first two actual polynomial coefficients can be replaced by evaluations in an etale coefficient chart. -/
theorem s2v_l1b_monic_coefficient_evaluation_etale
    {R A : Type} [CommRing R] [CommRing A]
    (n : ℕ) (f : R →+* A) (P : Polynomial A)
    (hP : P.Monic) (hdeg : P.natDegree = n + 2)
    (a b : R) (hab : IsUnit (b - a))
    (hEt : (MvPolynomial.eval₂Hom f (Sum.elim ![P.coeff 0, P.coeff 1]
      (fun k : Fin n => P.coeff (k.val + 2)))).Etale) :
    (MvPolynomial.eval₂Hom f (Sum.elim ![P.eval (f a), P.eval (f b)]
      (fun k : Fin n => P.coeff (k.val + 2)))).Etale := by
  classical
  have hrepr : P = Polynomial.X ^ (n + 2) + Polynomial.C (P.coeff 0) +
      Polynomial.C (P.coeff 1) * Polynomial.X +
      ∑ k : Fin n, Polynomial.C (P.coeff (k.val + 2)) * Polynomial.X ^ (k.val + 2) := by
    conv_lhs => rw [hP.as_sum, hdeg, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, pow_zero, pow_one, mul_one]
    rw [show (∑ k : Fin n, Polynomial.C (P.coeff (k.val + 2)) * Polynomial.X ^ (k.val + 2)) =
      ∑ k ∈ Finset.range n, Polynomial.C (P.coeff (k + 2)) * Polynomial.X ^ (k + 2) from
        Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (P.coeff (k + 2)) * Polynomial.X ^ (k + 2)) n]
    simp only [Nat.add_assoc, show 1 + 1 = 2 from rfl]
    ring
  have H := s2v_l1b_polynomial_evaluation_etale n f
    (Sum.elim ![P.coeff 0, P.coeff 1] (fun k : Fin n => P.coeff (k.val + 2)))
    a b hab hEt
  change (MvPolynomial.eval₂Hom f (Sum.elim ![_ , _] _)).Etale at H
  simpa only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ← hrepr] using H

end HodgeLean.Foundations.Program
