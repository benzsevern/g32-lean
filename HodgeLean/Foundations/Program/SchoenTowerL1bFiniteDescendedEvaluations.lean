import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteEvaluationCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1bDescendedEvaluationEtale

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A full tuple of distinct evaluations gives coordinates for the reversed symmetric expansion. -/
theorem s2v_l1b_finite_symmetric_evaluations_etale
    {K A : Type} [Field K] [CommRing A] (n : ℕ)
    (f : K →+* A) (c : Fin n → A) (a : Fin n → K)
    (ha : Function.Injective a) (hEt : (MvPolynomial.eval₂Hom f c).Etale) :
    (MvPolynomial.eval₂Hom f (fun i => (-f (a i)) ^ n +
      ∑ j : Fin n, c j * (-f (a i)) ^ (n - (j.val + 1)))).Etale := by
  have hrev : (MvPolynomial.eval₂Hom f (fun j => c (Fin.rev j))).Etale :=
    s2v_l1b_reindex_etale f c Fin.revPerm hEt
  have H := s2v_l1b_finite_evaluation_etale n f (fun j => c (Fin.rev j))
    (fun i => -a i) (fun i => (-a i) ^ n)
    (fun i j hij => ha (neg_injective hij)) hrev
  have hsum (i : Fin n) : (∑ j : Fin n, c j * (-f (a i)) ^ (n - (j.val + 1))) =
      ∑ j : Fin n, c (Fin.rev j) * (-f (a i)) ^ j.val := by
    rw [← Equiv.sum_comp Fin.revPerm]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  simpa only [map_pow, map_neg, hsum, mul_comm, add_comm] using H

/-- The actual descended branch polynomial has a full coordinate family of distinct evaluations. -/
theorem s2v_l1b_finite_descended_evaluations_etale
    {K A B L : Type} [Field K] [CommRing A] [CommRing B] [CommRing L]
    [Algebra K A] [Algebra K B] [Algebra K L]
    (n : ℕ) (z : Fin n → B) (q : A →ₐ[K] B)
    (hq : Function.Injective q) (P : Polynomial A)
    (hP : P.map q.toRingHom = ∏ i, (Polynomial.C (z i) - Polynomial.X))
    (c : Fin n → A)
    (hc : ∀ j, q (c j) = MvPolynomial.aeval (R := K) z
      (MvPolynomial.esymm (Fin n) K (j.val + 1)))
    (l : A →ₐ[K] L) (a : Fin n → K) (ha : Function.Injective a)
    (hEt : (MvPolynomial.eval₂Hom (algebraMap K L) (fun j => l (c j))).Etale) :
    (MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i => l (P.eval (algebraMap K A (a i))))).Etale := by
  have hev (t : K) : l (P.eval (algebraMap K A t)) =
      (-algebraMap K L t) ^ n +
        ∑ j : Fin n, l (c j) * (-algebraMap K L t) ^ (n - (j.val + 1)) := by
    rw [s2v_l1b_descended_product_expansion n z q hq P hP c hc t]
    simp only [map_add, map_sum, map_mul, map_pow, map_neg, l.commutes]
  simp only [hev]
  exact s2v_l1b_finite_symmetric_evaluations_etale n (algebraMap K L)
    (fun j => l (c j)) a ha hEt

end HodgeLean.Foundations.Program
